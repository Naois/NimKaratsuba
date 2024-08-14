import std/sequtils
import std/times

type BigInt = seq[uint64]
template tobigint(a: int) : BigInt = @[uint64(a)]
template tobigint(a: uint64) : BigInt = @[a]

# Note that for this and other comparison operators to work,
# Inputs must be normalised (i.e. have no trailing zeroes)

func `==`(a : BigInt, b : BigInt) : bool =
    if len(a) == len(b):
        for i in 0..len(a)-1:
            if a[i] != b[i]:
                return false
        return true
    return false

func `<`(a : BigInt, b : BigInt) : bool =
    if len(b) > len(a):
        return true
    if len(a) > len(b):
        return false
    let l = len(b)
    for i in 1..l:
        if b[l - i] > a[l - i]:
            return true
        elif b[l - i] < a[l - i]:
            return false
    return false

template `>`(a : BigInt, b : BigInt) : bool = b < a

func `<=`(a : BigInt, b : BigInt) : bool =
    if len(b) > len(a):
        return true
    if len(a) > len(b):
        return false
    let l = len(b)
    for i in 1..l:
        if b[l - i] > a[l - i]:
            return true
        elif b[l - i] < a[l - i]:
            return false
    return true

template `>=`(a : BigInt, b : BigInt) : bool = b <= a

template `shl`(a: BigInt, sh : int) : BigInt = (if a == 0.tobigint: a else: concat(newSeq[uint64](sh), a))

func `shr`(a: BigInt, sh : int) : BigInt =
    if len(a) <= sh:
        return 0.tobigint
    return a[sh..len(a)-1]

#Removes tailing zeroes
func normalize(a: var BigInt) =
    var i = len(a) - 1
    #Remove trailing zeroes
    while a[i] == 0 and i != 0:
        a.del(i)
        i -= 1

func `+`(a : BigInt, b : BigInt) : BigInt =
    let 
        lena = a.len()
        lenb = b.len()
        minlen = min(lena, lenb)
        maxlen = max(lena, lenb)
    var res : BigInt = @[]
    var carry : uint64 = 0
    for i in 0..minlen-1:
        res.add(a[i] + b[i])
        var temp = res[i] < a[i]
        res[i] += carry
        if res[i] < a[i]:
            temp = true
        if temp:
            carry = 1
        else:
            carry = 0
    if maxlen > minlen:
        if lena == maxlen:
            for i in minlen..maxlen-1:
                res.add(a[i] + carry)
                if res[i] < a[i]:
                    carry = 1
                else:
                    carry = 0
        else:
            for i in minlen..maxlen-1:
                res.add(b[i] + carry)
                if res[i] < b[i]:
                    carry = 1
                else:
                    carry = 0
    if carry > 0:
        res.add(carry)
    return res

func `-`(a : BigInt, b : BigInt) : BigInt =
    let 
        lena = a.len()
        lenb = b.len()
        minlen = min(lena, lenb)
        maxlen = max(lena, lenb)
    var res : BigInt = @[]
    var borrow : uint64 = 0
    for i in 0..minlen-1:
        res.add(a[i] - b[i])
        var temp = res[i] > a[i]
        res[i] -= borrow
        if res[i] > a[i]:
            temp = true
        if temp:
            borrow = 1
        else:
            borrow = 0
    if maxlen > minlen:
        if lena == maxlen:
            for i in minlen..maxlen-1:
                res.add(a[i]-borrow)
                if res[i] > a[i]:
                    borrow = 1
                else:
                    borrow = 0
        else:
            for i in minlen..maxlen-1:
                res.add(b[i]-borrow)
                if res[i] > b[i]:
                    borrow = 1
                else:
                    borrow = 0
    assert borrow == 0 #if this assert fails, then the result is a negative. Negatives are currently unimplemented.
    #Remove trailing zeroes
    res.normalize()
    return res

func tobigint(s: string) : BigInt =
    var res = 0.tobigint
    var base = 1.tobigint
    for i in 1..len(s):
        var digit = int(s[len(s)-i]) - int('0')
        for x in 1..digit:
            res = res + base
        #Compute base = 10*base without needing a multiplication method.
        let double = res + res
        let quad = double + double
        base = quad + quad + double
    return res

template Lo(n : uint64): uint64 =
    n and 0xFFFFFFFF'u64
template Hi(n : uint64): uint64 =
    n shr 32

# Multiplies two 64 bit ints together to produce a 128 bit int
func mult128(a : uint64, b : uint64) : BigInt =
    # Split a and b into High and Low 32 bit parts
    let
        aLo = a.Lo
        bLo = b.Lo
        aHi = a.Hi
        bHi = b.Hi
    var l = aLo * bLo + (Lo(aLo*bHi+bLo*aHi) shl 32)
    var h = aHi * bHi + (Hi(aLo*bHi+bLo*aHi))
    if aLo*bHi+bLo*aHi < aLo*bHi: 
        h += 1 shl 32
    if l < aLo * bLo: #This occurs when there is a carry producing l
        h += 1
    if h == 0:
        return @[l]
    return @[l, h]

func `*`(a : BigInt, b : BigInt) : BigInt =
    #Implementation of multiplication using the karatsuba method
    #Base case
    if len(a) == 1 and len(b) == 1:
        return(mult128(a[0],b[0]))
    #Firstly, we split each of a and b into two parts
    let z = max(len(a), len(b)) div 2
    var
        a1 : BigInt
        a2 : BigInt
        b1 : BigInt
        b2 : BigInt
    if len(a) > z:
        a1 = a[0..z-1]
        a2 = a[z..len(a)-1]
        a1.normalize()
    else:
        a1 = a
        a2 = 0.tobigint
    if len(b) > z:
        b1 = b[0..z-1]
        b2 = b[z..len(b)-1]
        b1.normalize()
    else:
        b1 = b
        b2 = 0.tobigint
    var a1b1 = a1*b1
    var a2b2 = a2*b2
    #Produces a1*b2+a2*b1, but only requires one multiplication instead of two.
    var rest = (a1 + a2)*(b1 + b2)
    rest = rest - a1b1 - a2b2
    a2b2 = a2b2 shl (2*z)
    rest = rest shl z
    return a2b2+a1b1+rest

func `*`(a : BigInt, x : uint64) : BigInt =
    var val = 0.tobigint
    for i in 0..len(a)-1:
        let incr = mult128(a[i], x)
        if len(incr) == 1:
            val[i] += incr[0]
            if val[i] < incr[0]:
                val.add(1)
            else:
                val.add(0)
        else:
            val[i] += incr[0]
            if val[i] < incr[0]:
                val.add(incr[1]+1)
            else:
                val.add(incr[1])
    val.normalize()
    return val

echo ((uint64(0) - uint64(1)).tobigint shl 1) + (uint64(0) - uint64(1)).tobigint + 1.tobigint