#!/usr/bin/env python3
"""ネットワーク対戦オセロ (TCPポート9801 / pygame)

サーバ用・クライアント用の区別なく、同じプログラムを両方で起動します。
最初の画面で「サーバになる」か「クライアントになる」を1クリックで選びます。
  - サーバ: 黒(先手)。ポート9801で待ち受け
  - クライアント: 白(後手)。入力欄のホストに接続 (既定 127.0.0.1)

使い方:  python3 othello_net.py [接続先ホスト]
"""
import queue
import socket
import sys
import threading

import pygame

PORT = 9801
N = 8
CELL = 70
MARGIN = 40
TOP = 90
W = MARGIN * 2 + CELL * N
H = TOP + CELL * N + MARGIN
EMPTY, BLACK, WHITE = 0, 1, 2
DIRS = [(-1, -1), (0, -1), (1, -1), (-1, 0), (1, 0), (-1, 1), (0, 1), (1, 1)]

GREEN = (20, 120, 60)
DARK = (10, 70, 35)
BG = (30, 30, 36)
WHITE_C = (240, 240, 240)
BLACK_C = (15, 15, 15)
HINT = (240, 220, 80)
BTN = (60, 90, 160)
BTN_HOVER = (85, 120, 200)


# ---------------- ゲームロジック ----------------
def new_board():
    b = [[EMPTY] * N for _ in range(N)]
    b[3][3] = b[4][4] = WHITE
    b[3][4] = b[4][3] = BLACK
    return b


def flips(b, x, y, p):
    """(x,y)に p が置いたとき裏返る座標のリスト。置けなければ空。"""
    if b[y][x] != EMPTY:
        return []
    q = 3 - p
    out = []
    for dx, dy in DIRS:
        line = []
        cx, cy = x + dx, y + dy
        while 0 <= cx < N and 0 <= cy < N and b[cy][cx] == q:
            line.append((cx, cy))
            cx += dx
            cy += dy
        if line and 0 <= cx < N and 0 <= cy < N and b[cy][cx] == p:
            out += line
    return out


def valid_moves(b, p):
    return [(x, y) for y in range(N) for x in range(N) if flips(b, x, y, p)]


def count(b):
    c = {BLACK: 0, WHITE: 0}
    for row in b:
        for v in row:
            if v:
                c[v] += 1
    return c


# ---------------- ネットワーク ----------------
class Net:
    """受信スレッドで改行区切りメッセージを queue に積む。"""

    def __init__(self):
        self.sock = None
        self.inbox = queue.Queue()
        self.lock = threading.Lock()

    def host(self):
        def run():
            try:
                srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                srv.bind(("", PORT))
                srv.listen(1)
                conn, _ = srv.accept()
                srv.close()
                self._start(conn)
            except OSError as e:
                self.inbox.put(("ERROR", str(e)))
        threading.Thread(target=run, daemon=True).start()

    def connect(self, host):
        def run():
            try:
                conn = socket.create_connection((host, PORT), timeout=10)
                conn.settimeout(None)
                self._start(conn)
            except OSError as e:
                self.inbox.put(("ERROR", str(e)))
        threading.Thread(target=run, daemon=True).start()

    def _start(self, conn):
        conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.sock = conn
        self.inbox.put(("CONNECTED", ""))
        buf = b""
        try:
            while True:
                data = conn.recv(1024)
                if not data:
                    break
                buf += data
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    parts = line.decode("utf-8", "replace").strip().split(None, 1)
                    if parts:
                        self.inbox.put((parts[0], parts[1] if len(parts) > 1 else ""))
        except OSError:
            pass
        self.inbox.put(("CLOSED", ""))

    def send(self, text):
        with self.lock:
            if self.sock:
                try:
                    self.sock.sendall((text + "\n").encode())
                except OSError:
                    pass

    def close(self):
        if self.sock:
            try:
                self.sock.close()
            except OSError:
                pass


# ---------------- UI ----------------
def pick_font(size):
    for name in ("notosanscjkjp", "notosansjp", "ipagothic", "ipaexgothic", "takaopgothic",
                 "meiryo", "yugothic", "msgothic", "hiraginosans", "applegothic"):
        path = pygame.font.match_font(name)
        if path:
            return pygame.font.Font(path, size), True
    return pygame.font.Font(None, size), False


def main():
    pygame.init()
    screen = pygame.display.set_mode((W, H))
    pygame.display.set_caption("Othello  (TCP %d)" % PORT)
    font, ja = pick_font(26)
    big, _ = pick_font(40)
    clock = pygame.time.Clock()

    def T(j, e):
        return j if ja else e

    host_text = sys.argv[1] if len(sys.argv) > 1 else "127.0.0.1"
    btn_server = pygame.Rect(W // 2 - 160, 200, 320, 70)
    btn_client = pygame.Rect(W // 2 - 160, 300, 320, 70)
    entry = pygame.Rect(W // 2 - 160, 420, 320, 40)

    net = Net()
    state = "menu"      # menu / waiting / playing / over / closed
    me = EMPTY
    board = new_board()
    turn = BLACK
    msg = ""

    def draw_text(s, f, color, center=None, topleft=None):
        img = f.render(s, True, color)
        r = img.get_rect()
        if center:
            r.center = center
        if topleft:
            r.topleft = topleft
        screen.blit(img, r)

    def advance():
        """手番交代。相手に手がなければ自動パス、両者なければ終局。"""
        nonlocal turn, state, msg
        nxt = 3 - turn
        if valid_moves(board, nxt):
            turn = nxt
            msg = ""
        elif valid_moves(board, turn):
            msg = T("パス: %sは置ける場所がありません" % ("黒" if nxt == BLACK else "白"),
                    "Pass: no moves for %s" % ("Black" if nxt == BLACK else "White"))
        else:
            state = "over"

    def place(x, y, p):
        for fx, fy in flips(board, x, y, p):
            board[fy][fx] = p
        board[y][x] = p
        advance()

    running = True
    while running:
        mouse = pygame.mouse.get_pos()
        for ev in pygame.event.get():
            if ev.type == pygame.QUIT:
                running = False
            elif state == "menu":
                if ev.type == pygame.KEYDOWN:
                    if ev.key == pygame.K_BACKSPACE:
                        host_text = host_text[:-1]
                    elif ev.unicode and ev.unicode.isprintable() and len(host_text) < 60:
                        host_text += ev.unicode
                elif ev.type == pygame.MOUSEBUTTONDOWN and ev.button == 1:
                    if btn_server.collidepoint(ev.pos):
                        me, state = BLACK, "waiting"
                        net.host()
                    elif btn_client.collidepoint(ev.pos):
                        me, state = WHITE, "waiting"
                        net.connect(host_text.strip() or "127.0.0.1")
            elif state == "playing" and ev.type == pygame.MOUSEBUTTONDOWN and ev.button == 1:
                x = (ev.pos[0] - MARGIN) // CELL
                y = (ev.pos[1] - TOP) // CELL
                if (turn == me and 0 <= x < N and 0 <= y < N and ev.pos[0] >= MARGIN
                        and ev.pos[1] >= TOP and flips(board, x, y, me)):
                    place(x, y, me)
                    net.send("MOVE %d %d" % (x, y))
            elif state in ("over", "closed") and ev.type == pygame.KEYDOWN and ev.key == pygame.K_ESCAPE:
                running = False

        # 受信処理
        while True:
            try:
                kind, arg = net.inbox.get_nowait()
            except queue.Empty:
                break
            if kind == "CONNECTED":
                state = "playing"
                board, turn, msg = new_board(), BLACK, ""
            elif kind == "ERROR":
                state = "closed"
                msg = T("接続エラー: ", "Connection error: ") + arg
            elif kind == "CLOSED":
                if state != "over":
                    state = "closed"
                    msg = T("相手との接続が切れました", "Disconnected from opponent")
            elif kind == "MOVE" and state == "playing":
                try:
                    x, y = map(int, arg.split())
                    if turn != me and 0 <= x < N and 0 <= y < N and flips(board, x, y, turn):
                        place(x, y, turn)
                except ValueError:
                    pass

        # 描画
        screen.fill(BG)
        if state == "menu":
            draw_text(T("ネットワーク対戦オセロ", "Network Othello"), big, WHITE_C, center=(W // 2, 100))
            draw_text("TCP port %d" % PORT, font, (180, 180, 180), center=(W // 2, 150))
            for r, label in ((btn_server, T("サーバになる (黒・先手)", "Be SERVER (Black)")),
                             (btn_client, T("クライアントになる (白)", "Be CLIENT (White)"))):
                pygame.draw.rect(screen, BTN_HOVER if r.collidepoint(mouse) else BTN, r, border_radius=10)
                draw_text(label, font, WHITE_C, center=r.center)
            draw_text(T("接続先ホスト (クライアント用):", "Host to connect (client):"),
                      font, (200, 200, 200), center=(W // 2, 400))
            pygame.draw.rect(screen, (245, 245, 245), entry, border_radius=6)
            draw_text(host_text + "|", font, BLACK_C, topleft=(entry.x + 10, entry.y + 8))
        elif state == "waiting":
            if me == BLACK:
                s = T("クライアントの接続を待っています… (port %d)" % PORT,
                      "Waiting for a client... (port %d)" % PORT)
            else:
                s = T("サーバに接続中…", "Connecting to server...")
            draw_text(s, font, WHITE_C, center=(W // 2, H // 2))
        else:
            pygame.draw.rect(screen, GREEN, (MARGIN, TOP, CELL * N, CELL * N))
            for i in range(N + 1):
                pygame.draw.line(screen, DARK, (MARGIN + i * CELL, TOP), (MARGIN + i * CELL, TOP + CELL * N), 2)
                pygame.draw.line(screen, DARK, (MARGIN, TOP + i * CELL), (MARGIN + CELL * N, TOP + i * CELL), 2)
            for y in range(N):
                for x in range(N):
                    c = (MARGIN + x * CELL + CELL // 2, TOP + y * CELL + CELL // 2)
                    if board[y][x]:
                        pygame.draw.circle(screen, BLACK_C if board[y][x] == BLACK else WHITE_C, c, CELL // 2 - 6)
            if state == "playing" and turn == me:
                for x, y in valid_moves(board, me):
                    pygame.draw.circle(screen, HINT, (MARGIN + x * CELL + CELL // 2,
                                                       TOP + y * CELL + CELL // 2), 6)
            cnt = count(board)
            mine = T("あなたは", "You are ") + (T("黒", "Black") if me == BLACK else T("白", "White"))
            draw_text(mine, font, WHITE_C, topleft=(MARGIN, 15))
            draw_text("%s %d  -  %s %d" % (T("黒", "B"), cnt[BLACK], T("白", "W"), cnt[WHITE]),
                      font, WHITE_C, topleft=(W - MARGIN - 190, 15))
            if state == "playing":
                s = T("あなたの番です", "Your turn") if turn == me else T("相手の番です", "Opponent's turn")
            elif state == "over":
                if cnt[BLACK] == cnt[WHITE]:
                    s = T("引き分け", "Draw")
                else:
                    win = BLACK if cnt[BLACK] > cnt[WHITE] else WHITE
                    s = T("あなたの勝ち！", "You win!") if win == me else T("あなたの負け", "You lose")
                s += T("  (Escで終了)", "  (Esc to quit)")
            else:
                s = msg
            draw_text(s, font, HINT, topleft=(MARGIN, 50))
            if msg and state == "playing":
                draw_text(msg, font, (255, 160, 160), topleft=(MARGIN, H - 32))
        pygame.display.flip()
        clock.tick(30)

    net.close()
    pygame.quit()


if __name__ == "__main__":
    main()
