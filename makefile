all: caxx paxx

caxx: caxx.c
	gcc -o caxx caxx.c -lm -O2
	sudo cp caxx /usr/bin/caxx
	sudo cp axx.1.gz /usr/share/man/man1/
paxx: axx.py
	sudo chmod +x axx.py
	sudo cp axx.py paxx
	sudo cp axx.py axx
	sudo cp paxx /usr/bin/paxx
	sudo cp axx.1.gz /usr/share/man/man1/
