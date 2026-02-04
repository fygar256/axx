all: caxx gaxx paxx

caxx: caxx.c
	cc -o caxx caxx.c -lm -O2
	sudo cp caxx /usr/local/bin/caxx
gaxx: gaxx.go
	go build -o gaxx gaxx.go
	sudo cp gaxx /usr/local/bin/gaxx
paxx: axx.py
	sudo cp axx.py paxx
	sudo cp paxx /usr/local/bin/paxx
