#!/usr/bin/env python3
import curses
import time
import random
import math
import sys
from collections import deque

# -----------------------------
# Configuration (tweak these)
# -----------------------------
ENEMY_COUNT = 6
BOMB_FUSE = 2.0               # seconds until bomb explodes
BOMB_RADIUS = 3               # manhattan radius
FREEZE_SECONDS = 10.0         # freeze length for enemies
PLAYER_STEP_MIN = 0.06        # minimum seconds between player moves
ENEMY_STEP_INTERVAL = 0.55    # slower -> easier
BOMB_COOLDOWN = 2.2
PARTICLE_LIFE = 0.6
SIDE_PANEL_WIDTH = 30
MIN_GRID_W = 36
MIN_GRID_H = 18
PELLET_ANIM_FPS = 6.0
PELLET_COLOR_FPS = 2.0

# Pellet frames used for hypnotic animation (emoji or ASCII fallback)
PELLET_EMOJI_FRAMES = ['◐', '◓', '◑', '◒']
PELLET_ASCII_FRAMES = ['|', '/', '-', '\\']

# -----------------------------
# Safe curses helpers
# -----------------------------

def init_colors_safe():
    """Try to initialise a small palette and return whether colors are available."""
    ok = False
    try:
        curses.start_color()
        try:
            curses.use_default_colors()
        except Exception:
            pass
        if curses.has_colors():
            palette = [
                (curses.COLOR_YELLOW, -1),  # player
                (curses.COLOR_RED, -1),     # enemies
                (curses.COLOR_CYAN, -1),    # pellets/hud
                (curses.COLOR_GREEN, -1),   # bombs/explosion
                (curses.COLOR_MAGENTA, -1), # walls/background
                (curses.COLOR_WHITE, -1),   # particles/text
                (curses.COLOR_BLUE, -1),    # extra
            ]
            for i, (fg, bg) in enumerate(palette, start=1):
                try:
                    curses.init_pair(i, fg, bg)
                except curses.error:
                    pass
            ok = True
    except Exception:
        ok = False
    return ok


def color_pair(idx, colors_enabled):
    return curses.color_pair(idx) if colors_enabled else 0


def safe_addstr(scr, y, x, s, attr=0):
    try:
        scr.addstr(y, x, s, attr)
    except curses.error:
        pass


def safe_addch(scr, y, x, ch, attr=0):
    try:
        scr.addch(y, x, ch, attr)
    except curses.error:
        try:
            scr.addstr(y, x, ch, attr)
        except curses.error:
            pass

# -----------------------------
# Maze generation
# -----------------------------

def build_playfield(width, height, complexity=0.75, density=0.75):
    """Return a grid of characters: '#' for wall, ' ' for floor.
    This makes walls render as a clear block (we draw them with reverse-space later).
    """
    grid = [['#' for _ in range(width)] for __ in range(height)]
    comp = int(complexity * (5 * (width + height)))
    dens = int(density * ((width // 2) * (height // 2)))

    for _ in range(dens):
        x = random.randrange(1, max(2, width // 2)) * 2
        y = random.randrange(1, max(2, height // 2)) * 2
        if 0 <= x < width and 0 <= y < height:
            grid[y][x] = ' '
            for _j in range(comp):
                neighbors = []
                if x > 1:
                    neighbors.append((x - 2, y))
                if x < width - 2:
                    neighbors.append((x + 2, y))
                if y > 1:
                    neighbors.append((x, y - 2))
                if y < height - 2:
                    neighbors.append((x, y + 2))
                if neighbors:
                    nx, ny = random.choice(neighbors)
                    if grid[ny][nx] == '#':
                        grid[ny][nx] = ' '
                        grid[(ny + y) // 2][(nx + x) // 2] = ' '
                        x, y = nx, ny

    # carve some longer corridors to open the map up
    for _ in range(max(10, (width * height) // 80)):
        wx = random.randint(1, width - 2)
        hy = random.randint(1, height - 2)
        length = random.randint(3, min(12, max(3, width // 4)))
        dx, dy = random.choice([(1, 0), (-1, 0), (0, 1), (0, -1)])
        x, y = wx, hy
        for __ in range(length):
            if 1 <= x < width - 1 and 1 <= y < height - 1:
                grid[y][x] = ' '
            x += dx; y += dy

    # border walls
    for x in range(width):
        grid[0][x] = '#'; grid[height - 1][x] = '#'
    for y in range(height):
        grid[y][0] = '#'; grid[y][width - 1] = '#'
    return grid

# -----------------------------
# Simple bounded BFS for pathfinding
# -----------------------------

def bfs_next_step(grid, src, dst, max_nodes=800):
    if src == dst:
        return src
    H = len(grid); W = len(grid[0])
    q = deque([src])
    parent = {src: None}
    nodes = 0
    while q and nodes < max_nodes:
        nodes += 1
        x, y = q.popleft()
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            nx, ny = x + dx, y + dy
            if 0 <= nx < W and 0 <= ny < H and grid[ny][nx] == ' ' and (nx, ny) not in parent:
                parent[(nx, ny)] = (x, y)
                if (nx, ny) == dst:
                    cur = (nx, ny)
                    while parent[cur] != src:
                        cur = parent[cur]
                    return cur
                q.append((nx, ny))
    # fallback: greedy neighbor
    sx, sy = src; gx, gy = dst
    best = None; bestd = abs(sx - gx) + abs(sy - gy)
    for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        nx, ny = sx + dx, sy + dy
        if 0 <= nx < W and 0 <= ny < H and grid[ny][nx] == ' ':
            d = abs(nx - gx) + abs(ny - gy)
            if d < bestd:
                bestd = d; best = (nx, ny)
    return best

# -----------------------------
# Game object
# -----------------------------
class PacGhostRefined:
    def __init__(self, stdscr):
        self.stdscr = stdscr
        self.colors = init_colors_safe()
        self.cp = lambda n: color_pair(n, self.colors)

        scr_h, scr_w = stdscr.getmaxyx()
        grid_w = max(MIN_GRID_W, scr_w - SIDE_PANEL_WIDTH - 6)
        grid_h = max(MIN_GRID_H, scr_h - 6)
        self.grid_w = grid_w; self.grid_h = grid_h

        self.grid = build_playfield(grid_w, grid_h)
        self.pellets = {(x, y) for y in range(grid_h) for x in range(grid_w) if self.grid[y][x] == ' '}

        # player spawn (center-ish)
        px, py = grid_w // 2, grid_h // 2
        if self.grid[py][px] != ' ':
            found = False
            for r in range(1, max(grid_w, grid_h)):
                for dx in range(-r, r + 1):
                    for dy in range(-r, r + 1):
                        nx, ny = px + dx, py + dy
                        if 0 <= nx < grid_w and 0 <= ny < grid_h and self.grid[ny][nx] == ' ':
                            px, py = nx, ny; found = True; break
                    if found: break
                if found: break
        self.player = {'x': px, 'y': py}
        if (px, py) in self.pellets:
            self.pellets.remove((px, py))

        # enemies spawn away from player
        candidates = [(x, y) for y in range(grid_h) for x in range(grid_w)
                      if self.grid[y][x] == ' ' and abs(x - px) + abs(y - py) > 8]
        random.shuffle(candidates)
        self.enemies = []
        for _ in range(ENEMY_COUNT):
            if not candidates: break
            gx, gy = candidates.pop()
            self.enemies.append({'x': gx, 'y': gy, 'freeze_until': 0.0, 'move_cool': 0.0})

        # visual items
        self.bombs = []          # dicts with x,y,placed,explode_at
        self.explosions = []    # ephemeral
        self.particles = []     # ephemeral

        self.last_bomb_time = -999.0
        self.last_player_move = 0.0
        self.start_time = time.time()
        self.score = 0
        self.paused = False
        self.game_over = False
        self.win = False

        # emoji support detection
        self.use_emoji = True
        try:
            stdscr.addstr(0, 0, '◉')
        except Exception:
            self.use_emoji = False

        self.pellet_frames = PELLET_EMOJI_FRAMES if self.use_emoji else PELLET_ASCII_FRAMES
        # color cycle indices (choose sensible color pair numbers)
        self.pellet_color_cycle = [3, 6, 3, 2]

        self.player_char = '👻' if self.use_emoji else 'P'
        self.enemy_chars = ['👾', '😈'] if self.use_emoji else ['E', 'e']
        self.bomb_char = '💣' if self.use_emoji else 'B'
        self.explosion_char = '✺' if self.use_emoji else '*'

    # ------------------ gameplay helpers
    def place_bomb(self):
        now = time.time()
        if now - self.last_bomb_time < BOMB_COOLDOWN:
            return
        x, y = self.player['x'], self.player['y']
        if self.grid[y][x] != ' ':
            return
        self.bombs.append({'x': x, 'y': y, 'placed': now, 'explode_at': now + BOMB_FUSE})
        self.last_bomb_time = now

    def move_player(self, dx, dy):
        if self.paused or self.game_over:
            return
        now = time.time()
        if now - self.last_player_move < PLAYER_STEP_MIN:
            return
        nx = self.player['x'] + dx
        ny = self.player['y'] + dy
        if 0 <= nx < self.grid_w and 0 <= ny < self.grid_h and self.grid[ny][nx] == ' ':
            self.player['x'], self.player['y'] = nx, ny
            if (nx, ny) in self.pellets:
                self.pellets.remove((nx, ny))
                self.score += 1
                # spawn particles for delight
                for _ in range(6):
                    ang = random.random() * 2 * math.pi
                    vx = math.cos(ang) * (0.3 + random.random() * 0.7)
                    vy = math.sin(ang) * (0.3 + random.random() * 0.7)
                    self.particles.append({'x': nx, 'y': ny, 'vx': vx, 'vy': vy, 'expire': time.time() + PARTICLE_LIFE})
        self.last_player_move = now

    def _explode_bombs(self):
        now = time.time()
        for b in list(self.bombs):
            if now >= b['explode_at']:
                bx, by = b['x'], b['y']
                expire = now + 0.6
                for dx in range(-BOMB_RADIUS, BOMB_RADIUS + 1):
                    for dy in range(-BOMB_RADIUS, BOMB_RADIUS + 1):
                        if abs(dx) + abs(dy) <= BOMB_RADIUS:
                            ex, ey = bx + dx, by + dy
                            if 0 <= ex < self.grid_w and 0 <= ey < self.grid_h:
                                self.explosions.append({'x': ex, 'y': ey, 'expire': expire})
                # freeze nearby enemies
                for en in self.enemies:
                    if abs(en['x'] - bx) + abs(en['y'] - by) <= BOMB_RADIUS:
                        en['freeze_until'] = now + FREEZE_SECONDS
                # player killed if inside blast
                if abs(self.player['x'] - bx) + abs(self.player['y'] - by) <= BOMB_RADIUS:
                    self.game_over = True
                    self.win = False
                try:
                    self.bombs.remove(b)
                except ValueError:
                    pass

    def _update_particles_and_explosions(self):
        now = time.time()
        self.explosions = [e for e in self.explosions if e['expire'] > now]
        for p in list(self.particles):
            p['x'] += p['vx']; p['y'] += p['vy']
            if now > p['expire']:
                try: self.particles.remove(p)
                except: pass

    def _move_enemies(self):
        now = time.time()
        for en in self.enemies:
            if en['freeze_until'] > now:
                continue
            if now < en['move_cool']:
                continue
            if random.random() < 0.7:
                nxt = bfs_next_step(self.grid, (en['x'], en['y']), (self.player['x'], self.player['y']), max_nodes=500)
                if nxt:
                    en['x'], en['y'] = nxt
                else:
                    dirs = [(1,0),(-1,0),(0,1),(0,-1)]
                    random.shuffle(dirs)
                    for dx,dy in dirs:
                        nx, ny = en['x']+dx, en['y']+dy
                        if 0 <= nx < self.grid_w and 0 <= ny < self.grid_h and self.grid[ny][nx] == ' ':
                            en['x'], en['y'] = nx, ny
                            break
            else:
                # small random wander to reduce frustration
                dirs = [(1,0),(-1,0),(0,1),(0,-1)]
                random.shuffle(dirs)
                for dx,dy in dirs:
                    nx, ny = en['x']+dx, en['y']+dy
                    if 0 <= nx < self.grid_w and 0 <= ny < self.grid_h and self.grid[ny][nx] == ' ':
                        en['x'], en['y'] = nx, ny
                        break
            en['move_cool'] = now + ENEMY_STEP_INTERVAL

    def step(self):
        if self.paused or self.game_over:
            return
        self._explode_bombs()
        self._update_particles_and_explosions()
        self._move_enemies()

        # collisions: enemy touches player -> death
        for en in self.enemies:
            if en['x'] == self.player['x'] and en['y'] == self.player['y']:
                self.game_over = True; self.win = False
                return

        # win condition
        if not self.pellets:
            self.game_over = True; self.win = True

    # ------------------ Drawing
    def _draw_side_panel(self, ox, oy, height, width):
        scr = self.stdscr
        try:
            for i in range(width):
                safe_addch(scr, oy, ox + i, '─')
                safe_addch(scr, oy + height - 1, ox + i, '─')
            for j in range(height):
                safe_addch(scr, oy + j, ox, '│'); safe_addch(scr, oy + j, ox + width - 1, '│')
            safe_addch(scr, oy, ox, '┌'); safe_addch(scr, oy, ox + width - 1, '┐')
            safe_addch(scr, oy + height - 1, ox, '└'); safe_addch(scr, oy + height - 1, ox + width - 1, '┘')
        except curses.error:
            pass
        safe_addstr(scr, oy + 1, ox + 2, "PACGHOST REFINED", self.cp(1) | curses.A_BOLD)
        safe_addstr(scr, oy + 3, ox + 2, f"Score: {self.score}", self.cp(3))
        safe_addstr(scr, oy + 4, ox + 2, f"Pellets: {len(self.pellets)}", self.cp(3))
        cooldown = max(0, round(max(0, (self.last_bomb_time + BOMB_COOLDOWN) - time.time()), 1)) if hasattr(self, 'last_bomb_time') else 0
        safe_addstr(scr, oy + 5, ox + 2, f"BombCD: {cooldown}s", self.cp(4))
        safe_addstr(scr, oy + 7, ox + 2, "Controls:", self.cp(6) | curses.A_BOLD)
        safe_addstr(scr, oy + 8, ox + 2, "Arrows: Move", self.cp(3))
        safe_addstr(scr, oy + 9, ox + 2, "b: Bomb (freeze)", self.cp(3))
        safe_addstr(scr, oy + 10, ox + 2, "p: Pause", self.cp(3))
        safe_addstr(scr, oy + 11, ox + 2, "r: Replay", self.cp(3))
        safe_addstr(scr, oy + 12, ox + 2, "q: Quit", self.cp(3))
        elapsed = time.time() - self.start_time
        safe_addstr(scr, oy + height - 3, ox + 2, f"Time: {int(elapsed) // 60:02d}:{int(elapsed) % 60:02d}", self.cp(6))

    def draw(self):
        scr = self.stdscr
        scr.erase()
        sh, sw = scr.getmaxyx()
        origin_x = max(2, (sw - self.grid_w - SIDE_PANEL_WIDTH) // 2)
        origin_y = max(2, (sh - self.grid_h) // 2)

        # draw the world
        for y in range(self.grid_h):
            for x in range(self.grid_w):
                ch = self.grid[y][x]
                sx = origin_x + x; sy = origin_y + y
                if ch == '#':
                    # solid visually: render as reverse-space for strong boundary
                    safe_addch(scr, sy, sx, ' ', self.cp(5) | curses.A_REVERSE)
                else:
                    if (x, y) in self.pellets:
                        t = time.time()
                        frame = int(t * PELLET_ANIM_FPS) % len(self.pellet_frames)
                        glyph = self.pellet_frames[frame]
                        color_idx = int((t * PELLET_COLOR_FPS) % len(self.pellet_frames))
                        col = self.pellet_color_cycle[color_idx] if hasattr(self, 'pellet_color_cycle') else 3
                        safe_addch(scr, sy, sx, glyph, self.cp(col) | curses.A_BOLD)
                    else:
                        safe_addch(scr, sy, sx, ' ')

        # particles
        for p in self.particles:
            px = int(round(p['x'])); py = int(round(p['y']))
            sx = origin_x + px; sy = origin_y + py
            safe_addch(scr, sy, sx, '.', self.cp(6))

        # bombs
        for b in self.bombs:
            bx = origin_x + b['x']; by = origin_y + b['y']
            safe_addch(scr, by, bx, self.bomb_char, self.cp(4) | curses.A_BOLD)
            # small fuse indicator
            rem = max(0, b['explode_at'] - time.time())
            if rem < 1.5:
                try:
                    safe_addch(scr, by, bx + 1, '.', self.cp(4))
                except curses.error:
                    pass

        # explosions
        now = time.time()
        for e in self.explosions:
            ex = origin_x + e['x']; ey = origin_y + e['y']
            safe_addch(scr, ey, ex, self.explosion_char, self.cp(4) | curses.A_BOLD)

        # enemies
        for en in self.enemies:
            gx = origin_x + en['x']; gy = origin_y + en['y']
            if en['freeze_until'] > now:
                ch = 'z' if not self.use_emoji else '🧊'
                safe_addch(scr, gy, gx, ch, self.cp(2))
            else:
                anim = int(time.time() * 3) % len(self.enemy_chars)
                safe_addch(scr, gy, gx, self.enemy_chars[anim], self.cp(2) | curses.A_BOLD)

        # player
        px = origin_x + self.player['x']; py = origin_y + self.player['y']
        safe_addch(scr, py, px, self.player_char, self.cp(1) | curses.A_BOLD)

        # side panel
        panel_x = origin_x + self.grid_w + 2
        panel_y = origin_y
        self._draw_side_panel(panel_x, panel_y, max(14, self.grid_h), SIDE_PANEL_WIDTH)

        if self.paused:
            safe_addstr(scr, origin_y + self.grid_h // 2, origin_x + max(2, self.grid_w // 2 - 6), " -- PAUSED -- ", self.cp(3) | curses.A_REVERSE)

        scr.refresh()

# -----------------------------
# Loop and entry
# -----------------------------

def play_round(stdscr):
    game = PacGhostRefined(stdscr)
    last_tick = time.time()
    try:
        while True:
            c = stdscr.getch()
            if c != -1:
                if c in (ord('q'), ord('Q')):
                    return 'quit', 0
                if c in (ord('p'), ord('P')):
                    game.paused = not game.paused
                if game.game_over:
                    pass
                else:
                    if c == ord('b'):
                        game.place_bomb()
                    elif c == curses.KEY_UP:
                        game.move_player(0, -1)
                    elif c == curses.KEY_DOWN:
                        game.move_player(0, 1)
                    elif c == curses.KEY_LEFT:
                        game.move_player(-1, 0)
                    elif c == curses.KEY_RIGHT:
                        game.move_player(1, 0)
            now = time.time()
            if now - last_tick >= 0.04:
                game.step()
                last_tick = now
            game.draw()
            if game.game_over:
                stdscr.nodelay(False)
                if game.win:
                    elapsed = time.time() - game.start_time
                    safe_addstr(stdscr, 1, 2, f" YOU WIN! Score: {game.score}  Time: {int(elapsed)//60:02d}:{int(elapsed)%60:02d} ", game.cp(1) | curses.A_BOLD)
                    safe_addstr(stdscr, 2, 2, " Press R to Replay or Q to Quit ", game.cp(3))
                else:
                    safe_addstr(stdscr, 1, 2, f" GAME OVER! Score: {game.score} ", game.cp(2) | curses.A_BOLD)
                    safe_addstr(stdscr, 2, 2, " Press R to Replay or Q to Quit ", game.cp(3))
                stdscr.refresh()
                while True:
                    k = stdscr.getch()
                    if k in (ord('r'), ord('R')):
                        return 'replay', game.score
                    if k in (ord('q'), ord('Q')):
                        return 'quit', game.score
                    time.sleep(0.05)
            time.sleep(0.01)
    except KeyboardInterrupt:
        return 'quit', 0


def main(stdscr):
    curses.curs_set(0)
    stdscr.nodelay(True)
    stdscr.keypad(True)
    init_colors_safe()
    while True:
        action, _ = play_round(stdscr)
        if action == 'quit':
            break
        if action == 'replay':
            continue
    try:
        curses.endwin()
    except Exception:
        pass


if __name__ == '__main__':
    try:
        curses.wrapper(main)
    except Exception as exc:
        try: curses.endwin()
        except Exception: pass
        print('Fatal error:', exc)
        sys.exit(1)
