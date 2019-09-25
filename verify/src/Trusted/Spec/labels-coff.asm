.686
.xmm
.model flat
.data

externdef dataSectionBase@GC@Systems_StaticData : NEAR
externdef dataSectionEnd@GC@Systems_StaticData : NEAR
externdef staticDataPointerBitMap : NEAR
externdef returnAddressToCallSiteSetNumbers : NEAR
externdef activationDescriptorTable : NEAR
externdef callSiteSetCount : NEAR
externdef callSetSiteNumberToIndex : NEAR

PUBLIC _$$?sectionCount
PUBLIC _$$?dataSectionBase
PUBLIC _$$?dataSectionEnd
PUBLIC _$$?staticDataPointerBitMap
PUBLIC _$$?callSiteTableCount
PUBLIC _$$?callSiteSetNumberToIndex
PUBLIC _$$?activationDescriptorTable
PUBLIC _$$?codeBaseStartTable
PUBLIC _$$?callSiteSetCount
PUBLIC _$$?returnAddressToCallSiteSetNumbers

;; One static data section

dataBaseTable label dword
dword dataSectionBase@GC@Systems_StaticData

dataEndTable label dword
dword dataSectionEnd@GC@Systems_StaticData

dataBitmapTable label dword
dword staticDataPointerBitMap

_$$?sectionCount label dword
dword 1

_$$?dataSectionBase label dword
dword dataBaseTable

_$$?dataSectionEnd label dword
dword dataEndTable

_$$?staticDataPointerBitMap label dword
dword dataBitmapTable


;; One call site table

returnAddressToCallSiteSetNumbersTable label dword
dword returnAddressToCallSiteSetNumbers

activationDescriptorTableTable label dword
dword activationDescriptorTable

codeBaseStartTableTable label dword
dword 00301000h ; all return addresses measured relative to this magic address.  TODO: don't hard-code this

callSiteSetCountTable label dword
dword callSiteSetCount

callSiteSetNumberToIndexTable label dword
dword callSetSiteNumberToIndex


_$$?callSiteTableCount label dword
dword 1

_$$?callSiteSetNumberToIndex label dword
dword callSiteSetNumberToIndexTable

_$$?activationDescriptorTable label dword
dword activationDescriptorTableTable

_$$?codeBaseStartTable label dword
dword codeBaseStartTableTable

_$$?callSiteSetCount label dword
dword callSiteSetCountTable

_$$?returnAddressToCallSiteSetNumbers label dword
dword returnAddressToCallSiteSetNumbersTable

end
