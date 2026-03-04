# rastreamento.py

import os
import re
import time
import json
import base64
import random
import threading
import gspread
import hashlib

from datetime import datetime
from zoneinfo import ZoneInfo
from selenium import webdriver
from gspread.utils import rowcol_to_a1
from gspread.exceptions import APIError
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.service import Service
from google.oauth2.service_account import Credentials
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager
from concurrent.futures import ThreadPoolExecutor, as_completed
from selenium.webdriver.support import expected_conditions as EC

# ==================================================
# VALIDACAO DE ENV (fail fast)
# ==================================================
REQUIRED_ENVS = [
    "SPREADSHEET_ID",
    "GCP_SERVICE_ACCOUNT_BASE64",
]

missing = [env for env in REQUIRED_ENVS if not os.environ.get(env)]

if missing:
    raise RuntimeError(
        f"Variáveis de ambiente obrigatórias não definidas: {', '.join(missing)}"
    )
        
# ==================================================
# CONFIG
# ==================================================
TZ = ZoneInfo("America/Sao_Paulo")
BATCH_SIZE = 30
WAIT_SECONDS = 15
MAX_RETRIES = 5
BASE_BACKOFF = 2
MAX_WORKERS = 2
ABAS_RASTREAVEIS = [
    "PEDIDOS (GERAL)",
]

# ==================================================
# LOG
# ==================================================
def log(msg):
    print(msg, flush=True)


# ==================================================
# CONTROLE GLOBAL DE DRIVERS
# ==================================================
drivers_criados = []
drivers_lock = threading.Lock()
thread_local = threading.local()

def rodar_rastreamento_para_aba(nome_aba: str):
    global sheet, header
    global COL_LINK, COL_OBS, COL_STATUS_LOG
    global COL_DATA_EVENTO, COL_HASH, COL_ULTIMA_LEITURA
    global COL_ESTUDO_DE_CASO
    global index_por_pedido

    log(f"\n🔄 Iniciando rastreamento da aba: {nome_aba}")

    SPREADSHEET_ID = os.environ["SPREADSHEET_ID"].strip()
    sheet = client.open_by_key(SPREADSHEET_ID).worksheet(nome_aba)

    header = [h.strip() for h in sheet.row_values(1)]

    # ===== Mapear colunas pelo nome =====
    def get_col_index(nome_coluna):
        try:
            return header.index(nome_coluna.strip()) + 1
        except ValueError:
            raise RuntimeError(f"Coluna obrigatória não encontrada: {nome_coluna}")

    COL_PEDIDO = get_col_index("ORDER ID")
    COL_LINK = get_col_index("LINK")
    COL_OBS = get_col_index("ATUALIZAÇÃO")
    COL_STATUS_LOG = get_col_index("STATUS LOGÍSTICO")
    COL_ESTUDO_DE_CASO = get_col_index("ESTUDO DE CASO")
    COL_HASH = get_col_index("HASH DO EVENTO")
    COL_DATA_EVENTO = get_col_index("DATA DO EVENTO")
    COL_ULTIMA_LEITURA = get_col_index("ÚLTIMA LEITURA")

    # 🔒 Snapshot da planilha
    dados = sheet.get_all_values()
    linhas = dados[1:]

    # 🔒 Índice estável por pedido
    index_por_pedido = {}
    for i, row in enumerate(linhas, start=2):
        if len(row) >= COL_PEDIDO:
            pedido = str(row[COL_PEDIDO - 1]).strip()
            if pedido:
                index_por_pedido[pedido] = i

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = []
        for row in linhas:
            pedido = str(row[COL_PEDIDO - 1]).strip()
            if pedido:
                futures.append(
                    executor.submit(processar_linha, pedido, row)
                )

        for i, _ in enumerate(as_completed(futures), start=1):
            if i % BATCH_SIZE == 0:
                flush_updates()

    flush_updates()

# ==================================================
# SELENIUM FACTORY
# ==================================================
def create_driver():
    options = Options()
    options.add_argument("--headless")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--window-size=1920,1080")
    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=options)
    wait = WebDriverWait(driver, WAIT_SECONDS)
    return driver, wait


def get_driver():
    if not hasattr(thread_local, "driver"):
        driver, wait = create_driver()
        thread_local.driver = driver
        thread_local.wait = wait

        with drivers_lock:
            drivers_criados.append(driver)

        log("🧩 Driver criado para thread")

    return thread_local.driver, thread_local.wait

# ==================================================
# GOOGLE SHEETS
# ==================================================
def get_gspread_client():
    creds_dict = json.loads(
        base64.b64decode(os.environ["GCP_SERVICE_ACCOUNT_BASE64"]).decode()
    )

    creds = Credentials.from_service_account_info(
        creds_dict,
        scopes=[
            "https://www.googleapis.com/auth/spreadsheets",
            "https://www.googleapis.com/auth/drive",
        ],
    )

    return gspread.authorize(creds)


client = get_gspread_client()

# ==================================================
# REGRA DE NEGÓCIO — IMPORTAÇÃO
# ==================================================

FALHA_DEVOLUCAO = [
    "devolução",
    "devolucao",
    "retorno",
    "pacote devolvido",
    "objeto devolvido",
    "entregue ao remetente",
    "objeto entregue ao remetente",
    "assinada [devolução]",
    "[devolução]",
    "return",
    "reverse",
]

FALHA_IMPORTACAO = [
    "importação não autorizada",
    "pedido não autorizado",
    "devolução determinada pela autoridade competente",
    "falha ao limpar na importação",
    "retido pela alfândega",
]

FALHA_DESTRUIDO = [
    "pacote destruído",
    "objeto destruído",
]

# ==================================================
# HELPERS
# ==================================================
def get_text(parent, cls):
    try:
        return parent.find_element(By.CLASS_NAME, cls).text.strip()
    except Exception:
        return ""

def eh_entregue_valido(texto: str) -> bool:
    texto = normalizar_texto(texto)

    BLOQUEIOS = [
        "saiu para entrega",
        "em rota de entrega",
        "out for delivery",
        "aguardando entrega",
        "em rota",
    ]

    if any(b in texto for b in BLOQUEIOS):
        return False

    PADROES_ENTREGA = [
        "objeto entregue ao destinatario",
        "objeto entregue ao destinatário",
        "pedido entregue",
        "pacote entregue",
        "pacote entregue com sucesso",
        "entrega concluida",
        "entrega concluída",
        "o pacote foi assinado",
        "entregue ao destinatario",
        "entregue ao destinatário",
        "delivery successful",
        "delivered",
        "signed",
    ]

    return any(p in texto for p in PADROES_ENTREGA)

def detectar_tipo_falha(texto_eventos: str):
    texto = normalizar_texto(texto_eventos)

    # Detecta qualquer variação de devolução (devolvido, devolvindo, devolução etc.)
    if "devolv" in texto:
        return "DEVOLUÇÃO", "devolução em andamento"

    for termo in FALHA_DEVOLUCAO:
        if normalizar_texto(termo) in texto:
            return "DEVOLUÇÃO", termo

    for termo in FALHA_IMPORTACAO:
        if normalizar_texto(termo) in texto:
            return "IMPORTAÇÃO", termo

    for termo in FALHA_DESTRUIDO:
        if normalizar_texto(termo) in texto:
            return "DESTRUIDO", termo

    return None, ""

def normalizar_texto(s: str) -> str:
    s = (s or "").strip().lower()
    s = re.sub(r"\s+", " ", s)
    return s


def gerar_hash_evento(status_log: str, data_evento: str, label: str, desc: str, local: str) -> str:
    """
    Gera um hash único baseado no último evento.
    O hash muda se QUALQUER parte do evento mudar.
    """
    payload = "|".join([
        normalizar_texto(status_log),
        normalizar_texto(data_evento),
        normalizar_texto(label),
        normalizar_texto(desc),
        normalizar_texto(local),
    ])

    return hashlib.sha1(payload.encode("utf-8")).hexdigest()
    
# ==================================================
# BUFFER DE ESCRITA
# ==================================================
updates = []
lock_updates = threading.Lock()

def add_update(row, col, value):
    cell = rowcol_to_a1(row, col)
    with lock_updates:
        updates.append({
            "range": f"{sheet.title}!{cell}",
            "values": [[value]]
        })

def flush_updates():
    global updates

    with lock_updates:
        if not updates:
            return

        body = {
            "valueInputOption": "RAW",
            "data": updates
        }
        batch = updates
        updates = []

    for tentativa in range(1, MAX_RETRIES + 1):
        try:
            sheet.spreadsheet.values_batch_update(body)
            log(f"📤 Batch enviado ({len(batch)} ranges)")
            return
        except APIError:
            wait_time = (BASE_BACKOFF ** tentativa) + random.uniform(0, 1)
            log(f"⚠️ Erro Sheets (tentativa {tentativa}) – aguardando {wait_time:.1f}s")
            time.sleep(wait_time)

    log("❌ Falha definitiva ao escrever no Sheets")


def deve_rastrear(status_salvo, obs_atual, link):
    status = (status_salvo or "").strip().upper()

    # ⛔ Status terminal REAL
    if status in {"ENTREGUE", "FALHA"}:
        return False, "status terminal"

    if not link or not link.startswith("http"):
        return False, "link inválido"

    return True, "rastrear"

def resolver_status_logistico(eventos):

    ultimo = eventos[0].find_element(By.CLASS_NAME, "rptn-order-tracking-text")
    texto_ultimo = normalizar_texto(ultimo.text)

    # 1️⃣ ENTREGA sempre ganha
    if eh_entregue_valido(texto_ultimo):
        return "Entregue", ""

    # 2️⃣ FALHA se último evento for falha real
    tipo_falha, motivo_falha = detectar_tipo_falha(texto_ultimo)

    # Nunca retorna "FALHA" como status logístico
    if tipo_falha == "IMPORTAÇÃO":
        return "Em trânsito", "Falha na importação"
    elif tipo_falha in ["DEVOLUÇÃO", "DESTRUIDO"]:
        return "Em trânsito", "Falha na entrega"

    # 3️⃣ Retirada
    if any(p in texto_ultimo for p in [
        "aguardando retirada",
        "disponível para retirada",
    ]):
        return "Aguardando retirada", ""

    # 4️⃣ Tentativa de entrega
    if any(p in texto_ultimo for p in [
        "não entregue",
        "carteiro não atendido",
        "nova tentativa",
        "tentativa de entrega",
    ]):
        return "Em trânsito", "Falha na entrega"

    # 5️⃣ Padrão → Em trânsito
    return "Em trânsito", ""

def processar_linha(pedido, row):
    # Fala que essas variáveis são globais
    global COL_LINK, COL_OBS, COL_STATUS_LOG
    global COL_DATA_EVENTO, COL_HASH, COL_ULTIMA_LEITURA, COL_ESTUDO_DE_CASO, index_por_pedido

    row_atual = index_por_pedido.get(str(pedido).strip())
    if not row_atual:
        log(f"⚠️ Pedido {pedido} não encontrado (linha mudou)")
        return

    link = row[COL_LINK - 1] if len(row) >= COL_LINK else ""
    obs_atual = row[COL_OBS - 1] if len(row) >= COL_OBS else ""
    hash_salvo = row[COL_HASH - 1] if len(row) >= COL_HASH else ""
    status_salvo = row[COL_STATUS_LOG - 1] if len(row) >= COL_STATUS_LOG else ""

    link = (link or "").strip()
    obs_atual = (obs_atual or "").strip().lower()

    agora_str = datetime.now(TZ).replace(microsecond=0).isoformat()

    log(f"➡️ Pedido {pedido} | Linha {row_atual} | Status atual: {status_salvo or '—'}")

    rastrear, motivo = deve_rastrear(status_salvo, obs_atual, link)

    if not rastrear:
        log(f"⏭️ Linha {row_atual} ignorada ({motivo})")

        if motivo == "link inválido":
            add_update(row_atual, COL_OBS, "⚠️ Link inválido ou vazio")

        return

    # Sempre marca última leitura
    add_update(row_atual, COL_ULTIMA_LEITURA, agora_str)

    driver, wait = get_driver()

    try:
        log(f"🌐 Abrindo página de rastreio: {link}")
        driver.get(link)
        time.sleep(1)
        driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")

        wait.until(
            EC.presence_of_element_located((By.CSS_SELECTOR, ".rptn-order-tracking"))
        )
        log("📦 Container de rastreio carregado")

        wait.until(
            EC.presence_of_element_located((By.CSS_SELECTOR, ".rptn-order-tracking-event"))
        )

        eventos = driver.find_elements(By.CSS_SELECTOR, ".rptn-order-tracking-event")
        log(f"📊 Eventos encontrados: {len(eventos)}")

        if not eventos:
            add_update(row_atual, COL_OBS, "❌ ERRO DE RASTREAMENTO — Nenhum evento encontrado")
            add_update(row_atual, COL_ESTUDO_DE_CASO, "Erro no rastreio")
            return

        status_novo, motivo_falha = resolver_status_logistico(eventos)

        ultimo = eventos[0]
        log("🔎 Lendo último evento...")

        data = get_text(ultimo, "rptn-order-tracking-date")
        label = get_text(ultimo, "rptn-order-tracking-label")
        local = get_text(ultimo, "rptn-order-tracking-location")
        desc = get_text(ultimo, "rptn-order-tracking-description")
        log(f"📌 Evento capturado: {data} | {label} | {local}")

        hash_novo = gerar_hash_evento(status_novo, data, label, desc, local)

        if motivo_falha:
            texto_obs = " | ".join(p for p in [
                "🚨 EVENTO FINAL NO HISTÓRICO — PEDIDO NÃO SERÁ ENTREGUE",
                f"Motivo: {motivo_falha}",
                f"Último status exibido: {label}",
                f"Data: {data}",
                f"Local: {local}",
            ] if p)
        else:
            texto_obs = " | ".join(
                p for p in [
                    f"Data: {data}",
                    f"Status: {label}",
                    f"Local: {local}",
                    f"Descrição: {desc}",
                ] if p
            )

        # Só reage se hash mudou
        if (hash_salvo or "").strip() == (hash_novo or "").strip():
            return

        # Mudou → grava tudo
        add_update(row_atual, COL_OBS, texto_obs)
        add_update(row_atual, COL_STATUS_LOG, status_novo)
        add_update(row_atual, COL_DATA_EVENTO, data)
        add_update(row_atual, COL_HASH, hash_novo)

        # Grava falha apenas na coluna ESTUDO DE CASO
        if motivo_falha:
            add_update(row_atual, COL_ESTUDO_DE_CASO, motivo_falha)
        else:
            add_update(row_atual, COL_ESTUDO_DE_CASO, "")

    except Exception as e:
        log(f"❌ Erro linha {row_atual}: {e}")
        add_update(row_atual, COL_OBS, "❌ ERRO TÉCNICO — Falha ao consultar rastreio.")
        add_update(row_atual, COL_ESTUDO_DE_CASO, "Erro no rastreio")

if __name__ == "__main__":
    for aba in ABAS_RASTREAVEIS:
        try:
            rodar_rastreamento_para_aba(aba)
        except Exception as e:
            log(f"❌ Erro ao rastrear aba {aba}: {e}")

    for driver in drivers_criados:
        try:
            driver.quit()
        except Exception:
            pass

    log("🏁 Rastreamento finalizado para todas as abas")
