print "(** DO NOT MODIFY. AUTO GENERATED BY HexGen.py **)"
print "Require Import ZArith."
print "Local Open Scope Z_scope."
g = lambda z: "Definition h%s := %s."%(("0"*(2-len(hex(z)[2:]))) +hex(z)[2:].upper(),z)
for x in xrange(2**8):
    print g(x)
