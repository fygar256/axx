#!/usr/bin/env python3
# FreeBSD: /dev/input/event* をすべて監視し、少しでも入力があれば「Cracked」と表示する。
# 使い方: doas python3 cracked.py   (root 権限が必要な場合があります)

import glob
import os
import select
import sys


def open_devices():
    fds = {}
    for path in sorted(glob.glob("/dev/input/event*")):
        try:
            fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK)
            fds[fd] = path
        except OSError as e:
            print("open失敗: %s (%s)" % (path, e), file=sys.stderr)
    return fds


def main():
    fds = open_devices()
    if not fds:
        print("監視できる /dev/input/event* がありません。", file=sys.stderr)
        sys.exit(1)

    print("%d 個のデバイスを監視中..." % len(fds))
    try:
        while True:
            readable, _, _ = select.select(list(fds), [], [])
            for fd in readable:
                try:
                    data = os.read(fd, 4096)
                except BlockingIOError:
                    continue
                except OSError:
                    continue
                if data:
                    print("Cracked", flush=True)
    except KeyboardInterrupt:
        pass
    finally:
        for fd in fds:
            os.close(fd)


if __name__ == "__main__":
    main()
