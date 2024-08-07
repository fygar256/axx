#!/usr/bin/python3
import sys
pc=0
capital="ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lower="abcdefghijklmnopqrstuvwxyz"
alphabet=lower+capital
symbols={}


vars=[ 0 for i in range(26) ]

def get_vars(s):
    c=ord(s.upper())
    return vars[c-ord('A')]

def put_vars(s,v):
    global vars
    c=ord(s.upper())
    vars[c-ord('A')]=v
    return

def err(m):
    print(m)
    return -1

def factor(s,idx):
    if s[idx]=='-':
        (x,idx)=factor(s,idx+1)
        x=-x
    elif s[idx]=='~':
        (x,idx)=factor(s,idx+1)
        x=~x
    else:
        (x,idx)=factor1(s,idx)
    return (x,idx)

def factor1(s,idx):
    x = 0

    if s[idx]=='$':
        idx+=1
        x=pc
    elif s[idx]=='0' and (s[idx+1]=='x' or s[idx+1]=='X'):
        idx+=2
        while(s[idx].upper() in "0123456789ABCDEF"):
            x=16*x+(ord(s[idx])-0x30 if s[idx] in "0123456789" else ord(s[idx].upper())-0x41+10 )
            idx+=1

    elif s[idx] in "0123456789":
        while(s[idx] in "0123456789"):
            x=10*x+ord(s[idx])-0x30
            idx+=1
        a=1
        if (s[idx]=='.'):
            idx+=1
            while(s[idx] in "0123456789"):
                x+=(a/10)*(ord(s[idx])-0x30)
                a/=10
                idx+=1

    elif s[idx] in "abcdefghijklmnopqrstuvwxyz":
        x=vars[ord(s[idx].upper())-0x41]
        idx+=1
    elif s[idx]=='(':
        (x,idx)=expression(s,idx+1)
        if s[idx]!=')':
            err("Missing ')'.")
            idx=-1
        else:
            idx+=1
    return (x,idx)

def term0(s,idx):
    (x,idx)=factor(s,idx)
    while True:
        if (s[idx]=='*'):
            (t,idx)=factor(s,idx+1)
            x*=t
        elif (s[idx]=='/'):
            (t,idx)=factor(s,idx+1)
            if t==0:
                err("Division by 0 error.")
                idx=-1
                x=-1
            else:
                x//=t
        elif s[idx]=='%':
            (t,idx)=factor(s,idx+1)
            x=x%t
        else:
            break
    return (x,idx)

def term1(s,idx):
    (x,idx)=term0(s,idx)
    while True:
        if (s[idx]=='+'):
            (t,idx)=term0(s,idx+1)
            x+=t
        elif (s[idx]=='-'):
            (t,idx)=term0(s,idx+1)
            x-=t
        else:
            break
    return (x,idx)

def term2(s,idx):
    (x,idx)=term1(s,idx)
    while True:
        if (s[idx]=='<' and s[idx+1]=='<'):
            (t,idx)=term1(s,idx+2)
            x<<=t
        elif (s[idx]=='>' and s[idx+1]=='>'):
            (t,idx)=term1(s,idx+2)
            x>>=t
        else:
            break
    return (x,idx)

def term3(s,idx):
    (x,idx)=term2(s,idx)
    while True:
        if (s[idx]=='&' and s[idx+1]!='&'):
            (t,idx)=term2(s,idx+1)
            x=int(x)&int(t)
        else:
            break
    return (x,idx)


def term4(s,idx):
    (x,idx)=term3(s,idx)
    while True:
        if (s[idx]=='|' and s[idx+1]!='|'):
            (t,idx)=term3(s,idx+1)
            x=int(x)|int(t)
        else:
            break
    return (x,idx)

def term5(s,idx):
    (x,idx)=term4(s,idx)
    while True:
        if (s[idx]=='^'):
            (t,idx)=term4(s,idx+1)
            x=int(x)^int(t)
        else:
            break
    return (x,idx)

def term6(s,idx):
    (x,idx)=term5(s,idx)
    while True:
        if (s[idx]=='\''):
            (t,idx)=term5(s,idx+1)
            x=(x&~((~0)<<t))|((~0)<<t if (x>>(t-1)&1) else 0)
        else:
            break
    return (x,idx)

def term7(s,idx):
    (x,idx)=term6(s,idx)
    while True:
        if (s[idx]=='<' and s[idx+1]=='='):
            (t,idx)=term6(s,idx+2)
            x=x<=t
        elif (s[idx]=='<'):
            (t,idx)=term6(s,idx+1)
            x=x<t
        elif (s[idx]=='>' and s[idx+1]=='='):
            (t,idx)=term6(s,idx+2)
            x=x>=t
        elif (s[idx]=='>'):
            (t,idx)=term6(s,idx+1)
            x=x>t
        elif (s[idx]=='=' and s[idx+1]=='='):
            (t,idx)=term6(s,idx+2)
            x=x==t
        elif (s[idx]=='!' and s[idx+1]=='='):
            (t,idx)=term6(s,idx+2)
            x=x!=t
        else:
            break
    return (x,idx)

def term8(s,idx):
    if s[idx]=='!':
        (x,idx)=term8(s,idx+1)
        x=not x
    else:
        (x,idx)=term7(s,idx)
    return (x,idx)

def term9(s,idx):
    (x,idx)=term8(s,idx)
    while True:
        if (s[idx]=='&' and s[idx+1]=='&'):
            (t,idx)=term8(s,idx+2)
            x=x and t
        else:
            break
    return (x,idx)

def term10(s,idx):
    (x,idx)=term9(s,idx)
    while True:
        if (s[idx]=='|' and s[idx+1]=='|'):
            (t,idx)=term9(s,idx+2)
            x=x or t
        else:
            break
    return (x,idx)


def expression(s,idx):
    s+=chr(0)
    return term10(s,idx)

def issymbol(w):
    l=list(symbols.items())
    for i in l:
        if i[0]==w:
            return w
    return ''
    
def readfile(fn):
    f=open(fn,"rt")
    af=f.readlines()
    f.close()
    return af
    
def set_symbol(l):
    if not (len(l)>=1 and l[0]=='$'):
    	return
    idx=1
    l+=chr(0)
    (w,idx)=getword(l,1)
    if l[idx]=='=':
        idx+=1
        (v,idx)=expression(l,idx)
        symbols[w.upper()]=v

def remove_comment(l):
    idx=0
    while idx<len(l):
        if len(l[idx:])>2 and l[idx]=='/' and l[idx+1]=='/':
            if idx==0:
                return ""
            else:
                return l[0:idx-1]
        idx+=1
    return l

def readpat(fn):
    f=open(fn,"rt")
    p=[]
    while(l:=f.readline()):
        head=l[0]
        l=remove_comment(l)
        l=l.replace('\n','')
        s=l.split(' ')
        t=[ i for i in s if i]
        if head==' ':
            t=['']+t
        if len(t)==1:
            t=[t[0],'','','']
        elif len(t)==2:
            t=[t[0],'','',t[1]]
        elif len(t)==3:
            t=[t[0],t[1],'',t[2]]
        elif len(t)==4:
            pass
        p.append(t)
    f.close()
    return [i for i in p if i]

def makeobj(s):
    ch=','
    s+=chr(0)
    idx=0
    cnt=0
    while ch!=chr(0):
        (x,idx)=expression(s,idx)
        x=x&0xff
        print("0x%02x," % x,end='')
        cnt+=1
        ch=s[idx]
        if ch==',':
            idx+=1
    print("")
    return cnt

def getword(s,idx):
    t=""
    while s[idx].upper() in capital:
        t+=s[idx].upper()
        idx+=1
    return t,idx
    
def match(s,t):
    s+=chr(0)
    t+=chr(0)
    idx_s=0
    idx_t=0
    while True:
        a=t[idx_t]
        b=s[idx_s]
        if a==chr(0) and b==chr(0):
            return True
        if a in capital and a==b.upper():
            pass
        elif a==b:
            pass
        elif a in "abcdefghijklmn":
            (v,idx_s)=expression(s,idx_s)
            if idx_s==-1:
                return False
            put_vars(t[idx_t],v)
            idx_t+=1
            continue
        elif a in "opqrstuvwxyz":
            (w,idx_s)=getword(s,idx_s)
            if issymbol(w):
                put_vars(t[idx_t],symbols[w])
            idx_t+=1
            continue
        elif a!=b:
            return False
        idx_s+=1
        idx_t+=1

def errorchk(s):
    idx=0
    s+=chr(0)
    ef=False
    while True:
        (x,idx)=expression(s,idx)
        if s[idx]==';':
            idx+=1
            (e,idx)=expression(s,idx)
        if x:
            ef=True
            print(f"error code:{e}")
            if s[idx]==',':
                idx+=1
                continue
            break
        break
    return ef

def lineassemble(pat,line):
    if line=="" or line=="\n":
        return 0
    prev=''
    l=[i for i in line.replace('\n','').upper().split(' ') if i]
    idx=0
    of=0
    for i in pat:
        set_symbol(i[0])
        a=i[0]
        if a=='':
            a=prev
        prev=a
        if len(l)==0:
            continue
        if a==l[0]:
            if len(l)==1:
                of=makeobj(i[3])
                break
            elif len(l)==2 and match(l[1],i[1]):
                if not errorchk(i[2]):
                    of=makeobj(i[3])
                    break
    if not of:
        print("Mnemonic error.")
    return of

def main():
    global pc
    pc=0

    if len(sys.argv)==1:
        print("Usage: axx.py patternfile.axx [sourcefile.asm]")
        return

    if len(sys.argv)>=2:
        pat=readpat(sys.argv[1])
    if len(sys.argv)==2:
        while line:=input(":"):
            pc+=lineassemble(pat,line)
    elif len(sys.argv)==3:
        af=readfile(sys.argv[2])
        for i in af:
            pc+=lineassemble(pat,i)

if __name__=='__main__':
    main()
    exit(0)
