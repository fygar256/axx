all: caxx paxx

caxx: caxx.c
	gcc -o caxx caxx.c -lm -lquadmath -O2
paxx: axx.py
	chmod +x axx.py
	cp axx.py paxx
	cp axx.py axx
install:
	install paxx /usr/local/bin/paxx
	install axx.1.gz /usr/share/man/man1/
	install caxx /usr/local/bin/caxx
