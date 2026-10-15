#!/usr/bin/env python3
"""PNG画像をpygameで表示する。

使い方:  python3 show_png.py 画像1.png [画像2.png ...]
  ← / → : 画像の切り替え (複数指定時)
  + / - : 拡大・縮小
  Esc   : 終了
"""
import sys

import pygame


def main():
    if len(sys.argv) < 2:
        print("使い方: python3 show_png.py 画像.png [画像2.png ...]")
        return
    paths = sys.argv[1:]
    pygame.init()
    pygame.display.set_mode((640, 480))
    images = [pygame.image.load(p).convert() for p in paths]
    idx, scale = 0, 2

    def show():
        img = images[idx]
        w, h = img.get_size()
        screen = pygame.display.set_mode((w * scale, h * scale))
        pygame.display.set_caption("%s  (%d/%d)  x%d" % (paths[idx], idx + 1, len(paths), scale))
        screen.blit(pygame.transform.scale(img, (w * scale, h * scale)), (0, 0))
        pygame.display.flip()

    show()
    while True:
        for ev in pygame.event.get():
            if ev.type == pygame.QUIT or (ev.type == pygame.KEYDOWN and ev.key == pygame.K_ESCAPE):
                pygame.quit()
                return
            if ev.type == pygame.KEYDOWN:
                if ev.key == pygame.K_RIGHT:
                    idx = (idx + 1) % len(images)
                elif ev.key == pygame.K_LEFT:
                    idx = (idx - 1) % len(images)
                elif ev.key in (pygame.K_PLUS, pygame.K_EQUALS, pygame.K_KP_PLUS):
                    scale = min(scale + 1, 6)
                elif ev.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                    scale = max(scale - 1, 1)
                else:
                    continue
                show()
        pygame.time.wait(30)


if __name__ == "__main__":
    main()
