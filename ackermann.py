#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Dec  7 18:34:51 2017

@author: hd
"""
import sys
sys.setrecursionlimit(1000000)

succ=lambda n: (lambda x,h: (n(h(x),h)))

def entier_de_church(n):
    s=lambda x,h: x
    for i in range (n):
        s=succ(s)
    return s

ackermann=lambda m,n:((m(succ,lambda f: (lambda n: n(f(entier_de_church(1)),f))))(n))

ackermann=lambda m,n:m(succ,lambda f: succ(n)(entier_de_church(1),f))


a=entier_de_church(3)
b=entier_de_church(3)
print((ackermann (a,b))(0,lambda x : (x+1)))

def autre_ackermann(m,n):
    if m==0:
        return n+1
    elif n==0:
        return autre_ackermann(m-1,1)
    else:
        return autre_ackermann(m-1,autre_ackermann(m,n-1))

def test(n):
    for i in range (n):
        for j in range(i+1):
            if (ackermann(entier_de_church(i),entier_de_church(j))(0,lambda x :x+1))!=autre_ackermann(i,j):
                return False
    return True
