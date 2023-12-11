def _parse_macros(self):
    self._iter_lines(self._parse_macro)

def _parse_macro(self, line, p, o):
    self.allMacros = ["MV", "SWP", "SUM", "WHILE"]

    #provjera je li naredba uopće macro
    if line[0] != "$":
        return line
    
    #dohvaćanje macro naredbe
    label = line[1:]
    macroCommand = label.strip().split("(")[0]

    #provjera je li macro naredba uopće postoji (MV, SWP, SUM, WHILE)
    if macroCommand not in self.allMacros:
        self._flag = False
        self._line = o
        self._errm = "Unknown macro command"
        return line
    
    #popunjavanje liste argumenata
    argList = label.split('(', 1)[1].rsplit(')', 1)[0].split(',')
    for i in range(0, len(argList)):
        argList[i] = argList[i].strip()
    
    if(macroCommand == self.allMacros[0]):
        return self._parse_MV(argList, o, p)
    elif(macroCommand == self.allMacros[1]):
        return self._parse_SWP(argList, o, p)
    elif(macroCommand == self.allMacros[2]):
        return self._parse_SUM(argList, o, p)
    elif(macroCommand == self.allMacros[3]):
        return self._parse_WHILE(argList, o, p)
    elif(macroCommand == 'END'):
        return self._parse_END(argList, o, p)
    
def _parse_MV(self, argList, o, p):
    if len(argList) != 2:
        self._flag = False
        self._line = o
        self._errm = "Too many/few arguments"
        return
    
    a = argList[0]
    b = argList[1]

    return [
        "@" + a,
        "D=M",
        "@" + b,
        "M=D"
    ]

def _parse_SWP(self, argList, o, p):
    if len(argList) != 2:
        self._flag = False
        self._line = o
        self._errm = "Too many/few arguments"
        return
    
    a = argList[0]
    b = argList[1]

    return [
        "@" + a,
        "D=M",
        "@swap",
        "M = D",
        "@" + b,
        "D=M",
        "@" + a,
        "M=D",
        "@swap",
        "D=M",
        "@" + b,
        "M=D"
    ]

def _parse_SUM(self, argList, o, p):
    if len(argList) != 3:
        self._flag = False
        self._line = o
        self._errm = "Too many/few arguments"
        return
    
    a = argList[0]
    b = argList[1]
    c = argList[2]

    return [
        "@" + a,
        "D=M",
        "@" + b,
        "D=D+M",
        "@" + c,
        "M=D"
    ]