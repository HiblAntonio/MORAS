// D - podatkovni
// A - adresni/podatkovni (obična vrijednost)
// M - trenutno odabrani memorijski registar (RAM[A])

@0
D = M;

@1
D = M + D;

@2
D = M + D;

@3
D = M + D;

@4
D = M + D;

@5
M = D;

(END)
@END