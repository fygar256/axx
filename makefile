all: caxx paxx

caxx: caxx.c
	gcc -o caxx caxx.c -lm -lquadmath -O2
paxx: axx.py
	chmod +x axx.py
install:
	cp axx.py paxx
	cp axx.py axx
	cp paxx /usr/local/bin/paxx
	cp axx.1.gz /usr/share/man/man1/
	cp caxx /usr/local/bin/caxx
