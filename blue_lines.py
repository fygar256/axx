#!/usr/bin/env python3
"""PNG画像の黒い部分(背景)に、青い横線を縦間隔Nピクセルで引いて保存する。

黒以外の部分(文字など)はそのまま残ります。

使い方:  python3 blue_lines.py 入力.png N [出力.png]
  出力を省略すると「入力名_lines.png」に保存します。
  例: python3 blue_lines.py PJLOGO.png 8
"""
import os
import sys

import pygame

BLACK = (0, 0, 0)
BLUE = (0, 0, 255)


def draw_blue_lines(img, n):
    """img の黒ピクセルのうち、y が n の倍数の行を青にする。"""
    w, h = img.get_size()
    out = img.copy()
    for y in range(0, h, n):
        for x in range(w):
            if tuple(img.get_at((x, y)))[:3] == BLACK:
                out.set_at((x, y), BLUE)
    return out


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 1
    src = sys.argv[1]
    try:
        n = int(sys.argv[2])
        if n < 1:
            raise ValueError
    except ValueError:
        print("Nは1以上の整数で指定してください")
        return 1
    dst = sys.argv[3] if len(sys.argv) > 3 else os.path.splitext(src)[0] + "_lines.png"

    img = pygame.image.load(src)
    pygame.image.save(draw_blue_lines(img, n), dst)
    print("保存しました:", dst)
    return 0


if __name__ == "__main__":
    sys.exit(main())
