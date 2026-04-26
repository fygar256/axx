#!/usr/bin/python
import sys

pas=0
current_section=".text"
sections={ '.text' :['']}
capital="ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lower="abcdefghijklmnopqrstuvwxyz"
digit='0123456789'
alphabet=lower+capital
lwordchars=lower+capital+digit+"_"


def skipspc(s,idx):
    while len(s)>idx:
        if s[idx]==' ':
            idx+=1
            continue
        break
    return idx


def get_label_word(s,idx):
    idx=skipspc(s,idx)
    t=""
    if len(s)>idx and (s[idx]=='.' or s[idx] in lwordchars):
        t=s[idx]
        idx+=1
        while len(s)>idx:
            if not s[idx] in lwordchars: 
                break
            t+=s[idx]
            idx+=1
    return t,idx

def readsections(fn):
    global sections,current_section
    with open(fn,"rt") as file:
        while True:
            l=file.readline().replace(chr(13),'')
            if l=='':
                return True
            l=l.strip()

            (sec,idx)=get_label_word(l,0)
            if sec.upper()==".SECTION" or sec.upper()==".SEGMENT":
                (secname,idx)=get_label_word(l,idx)
                if secname==current_section:
                    continue
                else:
                    current_section=secname
                    continue
            elif sec.upper()==".LABELC":
                idx=skipspc(l,idx)
                ss=""
                while True:
                    if len(l)<=idx or l[idx]=='"':
                        break
                    ss+=l[idx]
                    idx+=1
                lwordchars=alphabet+digit+ss+"_"
                continue
            elif sec.upper()==".INCLUDE":
                idx=skipspc(l,idx)
                if l[idx]=='"':
                    idx+=1
                fn=""
                while True:
                    if len(l)<=idx or l[idx]=='"':
                        break
                    fn+=l[idx]
                    idx+=1
                readsections(fn)
            else:
                if current_section in sections:
                    sections[current_section]=sections[current_section]+[l]
                else:
                    sections[current_section]=[l]

def writesections():
    l=list(sections.items())
    for i in l:
        (a,b)=i
        print(".section    ",a)
        for k in b:
            print(k)

if __name__=='__main__':
    readsections(sys.argv[1])
    writesections()
