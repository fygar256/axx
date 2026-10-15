#!/usr/bin/env python3
# FreeBSD: /dev/input/event* をすべて監視し、最初の入力を検知したら
# 「Cracked」を1回だけ表示し、指定のメールアドレスに「Cracked」というメールを送って終了する。
#
# 使い方:
#   doas python3 cracked.py --to you@example.com
#   doas python3 cracked.py --to you@example.com --smtp-host smtp.example.com \
#        --smtp-port 587 --smtp-user USER --starttls     (パスワードは環境変数 SMTP_PASSWORD)
#
# --smtp-host を省略すると localhost:25 (FreeBSD の sendmail 等) を使います。

import argparse
import glob
import os
import select
import smtplib
import sys
from email.message import EmailMessage


def open_devices():
    fds = {}
    for path in sorted(glob.glob("/dev/input/event*")):
        try:
            fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK)
            fds[fd] = path
        except OSError as e:
            print("open失敗: %s (%s)" % (path, e), file=sys.stderr)
    return fds


def send_mail(args):
    msg = EmailMessage()
    msg["Subject"] = "Cracked"
    msg["From"] = args.sender or args.smtp_user or ("cracked@" + os.uname().nodename)
    msg["To"] = args.to
    msg.set_content("Cracked")

    with smtplib.SMTP(args.smtp_host, args.smtp_port, timeout=30) as s:
        if args.starttls:
            s.starttls()
        if args.smtp_user:
            s.login(args.smtp_user, os.environ.get("SMTP_PASSWORD", ""))
        s.send_message(msg)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--to", required=True, help="通知先メールアドレス")
    p.add_argument("--from", dest="sender", help="送信元メールアドレス")
    p.add_argument("--smtp-host", default="localhost")
    p.add_argument("--smtp-port", type=int, default=25)
    p.add_argument("--smtp-user")
    p.add_argument("--starttls", action="store_true")
    args = p.parse_args()

    fds = open_devices()
    if not fds:
        print("監視できる /dev/input/event* がありません。", file=sys.stderr)
        sys.exit(1)

    print("%d 個のデバイスを監視中..." % len(fds))
    detected = False
    try:
        while not detected:
            readable, _, _ = select.select(list(fds), [], [])
            for fd in readable:
                try:
                    data = os.read(fd, 4096)
                except OSError:
                    continue
                if data:
                    detected = True
                    break
    except KeyboardInterrupt:
        pass
    finally:
        for fd in fds:
            os.close(fd)

    if detected:
        print("Cracked", flush=True)
        try:
            send_mail(args)
            print("メールを送信しました: %s" % args.to)
        except Exception as e:
            print("メール送信に失敗しました: %s" % e, file=sys.stderr)
            sys.exit(2)


if __name__ == "__main__":
    main()
