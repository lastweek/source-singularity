#
# Simple script to find function associated with a function in .map file.
#
# Useful for when running in a simulator or with JTAG looking for errors
# before the debugger is attached.
#

import sys

def HexToLong(h):
    if len(h) > 2 and h[0:2] == "0x":
        return long(h[2:], 16)
    else:
        return long(h, 16)

def BuildSymbolMap(symbolMapFile):
    symbolMap = []

    for line in symbolMapFile:
        if line.find('?') < 0:
            continue
        components = line.split()
        mapEntry = (HexToLong(components[2]), components[1])
        symbolMap.append(mapEntry)

    return symbolMap

def FindMatch(symbolMap, lookupAddress):
    # Ripe for a modified binary search but horrible O(N) implementation now.
    lastAddress = 0
    lastSymbol  = "ScriptError"

    for address, symbol in symbolMap:
        if address == lookupAddress:
            return True, address, symbol
        elif lookupAddress < address:
            return True, lastAddress, lastSymbol
        lastAddress, lastSymbol = address, symbol

    return False, address, address

def FindOne(symbolMap, address):
    success, fnStartAddress, fnName = FindMatch(symbolMap, address)
    if success == True:
        print "%08x in %s + %03x" % (address, fnName, address - fnStartAddress)
    else:
        print "Match not found."

def AnnotatePrt(symbolMap, prt):
    for line in prt:
        if line.startswith("!(ETC) -"):
            try:
                address = HexToLong(line.split()[2])
                success, fnStart, fnName = FindMatch(symbolMap, address)
                if success:
                    print "%s [%08x + %08x]" % (fnName, fnStart, address - fnStart)
                print line.rstrip()
            except ValueError:
                print "Oops! \"%s\"" % line

def main(argv):
    if len(argv) != 3 and len(argv) != 4:
        print "Usage: %s <MapFile> <Address>"
        return -1

    if len(argv) == 3:
        dotMapFile  = open(argv[1], "r")
        address = HexToLong(argv[2])
        FindOne(BuildSymbolMap(dotMapFile), address)
        dotMapFile.close()

    if len(argv) == 4 and argv[1] == "-prt":
        dotMapFile  = open(argv[2], "r")
        prtFile = open(argv[3], "r")
        AnnotatePrt(BuildSymbolMap(dotMapFile), prtFile)
        dotMapFile.close()
        prtFile.close()

if __name__ == "__main__":
    sys.exit(main(sys.argv))
