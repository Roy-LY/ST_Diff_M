# -*- coding: utf-8 -*-
"""
Created on Sat Oct 14 2019
@author: Ling Song
"""
import math
import subprocess

# STATE_SIZE, BASE for Pi, IND for extraction, OUTPUT_SIZE, N rounds, OBJ type, CHI_EXTRA allowing at most 3,4 or 5 consecutive active ANDs
V = [[ 97, 15, 4, 12+1, 4], # 0   small  
     [193, 15, 4, 24+1, 3], # 1  middle
     [257, 12, 4, 32+1, 3]] # 2   big
base_list = [5, 7,  10, 13, 14,   15, 17, 21, 23, 26,   29, 37, 38, 39, 40,    41, 56, 57, 58, 59,    60, 68, 71, 74, 76,   80, 82, 83, 84, 87,   90, 92]  # 

NUM = 0

SUBTERRANEAN_SIZE = V[NUM][0]
#BASE =  V[NUM][1]  
IND = V[NUM][2]
#FACTOR = BASE**IND % SUBTERRANEAN_SIZE
OUTPUT_SIZE = V[NUM][3]
N = V[NUM][4]  # N rounds, N+1 blocks  
BOUND = 47  # update here



def int2vector(a):
    ret = ''
    for i in range(11):
        bit = (a>>i)&0x1
        ret = str(bit) + ret
    return '0bin'+ret

def declare_vars(f):
    f.write('% variables \n')
    names = ['A', 'B', 'C', 'D', 'Z', 'W']
    for i in range(N):  
        line = []   
        for j in range(len(names)):
            line.append( names[j]+str(i))
        f.write(', '.join(line)+': BITVECTOR(' + str(SUBTERRANEAN_SIZE) +');\n')
    f.write('D'+str(N) + ', '+'Z'+str(N)+ ', '+'A'+str(N)+': BITVECTOR(' + str(SUBTERRANEAN_SIZE) +');\n')
    
    f.write('% intermediate variables \n')
    names = ['pA']
    for i in range(N):  
        line = []   
        for j in range(len(names)):
            line.append( names[j]+str(i))
        f.write(', '.join(line)+': BITVECTOR(' + str(SUBTERRANEAN_SIZE) +');\n') 

    f.write('% weight variable \n')
    f.write('W: BITVECTOR(11);\n')

def constraintOf2Xor(a, b, c):
    """ for linear: a = b = c, for diff: a xor b = c
    for masks, a xor b xor c = 0 """
    constraint = []
    constraint.append("ASSERT( %s = BVXOR(%s, %s) );" % (c, a, b) )
    return constraint

def constraintOfMultiXorForStates(a, n):
    """a is a vector of n states
    linear: a[0] = a[1] = a[2] = ...
    diff: a[0] xor a[1] xor a[2] xor ... = 0
    for masks: a[0] xor a[1] xor a[2] xor ... = 0, the same as the constraints for long xor in diff analysis"""
    assert( n > 2 )
    constraint = []
    s = "BVXOR(%s, %s)" % (a[1], a[0])
    for i in range(2, n-1):
        s = "BVXOR(%s, %s)" % (a[i], s)
    constraint.append("ASSERT( %s = %s );" % (a[n-1], s))
    return constraint

def constraintOfAnd(a, b, c):
    """a, b, c are bits
    a and b = c"""
    constraint = []
    constraint.append("ASSERT( ~%s & ( %s | %s ) = %s );" % (c, a, b, zero_vector() ))
    return constraint

# 右循环移位
def rsr(x, n, N):
    return "( (%s << %d)[%d : 0] | (%s >> %d) )" % (x, N-n, N-1, x, n)

# 左循环移位
def lsr(x, n, N):
    return "( (%s << %d)[%d : 0] | (%s >> %d) )" % (x, n, N-1, x, N-n)

def constraintOfTheta(b, c, r):
    """  Ci = Bi + Bi+3 + Bi+8
    b: diff of the input of theta
    c: diff of the output of theta  """
    constraint = []
    constraint += constraintOfMultiXorForStates([b, rsr(b, 3, SUBTERRANEAN_SIZE), rsr(b, 8, SUBTERRANEAN_SIZE), c], 4)  
    return constraint

def Pi(A, base):
    B = [0 for i in range(SUBTERRANEAN_SIZE)]
    for x in range(SUBTERRANEAN_SIZE):
        B[x] = A[(base*x)%SUBTERRANEAN_SIZE]
    return B

def constraintOfPi(C, D, base):
    constraint = []
    #constraint.append("ASSERT( %s = %s);" % ( D, C )  )
    #print(base)
    for x in range(SUBTERRANEAN_SIZE):
        j = (base*x)%SUBTERRANEAN_SIZE
        constraint.append("ASSERT( %s[%d:%d] = %s[%d:%d] );" % ( D, x, x, C, j, j )  )
    return constraint

def constraintOfChi(a, pa, b, r):
    """
    a: diff of the input
    pa: output diff of AND operation
    b: output diff of chi
    """
    alpha = 2
    beta = 1
    constraint = []

    a_rotalpha = rsr(a, alpha, SUBTERRANEAN_SIZE)
    a_rotbeta = rsr(a, beta, SUBTERRANEAN_SIZE)

    #Deal with dependent inputs
    varibits = "({0} | {1})".format(a_rotalpha, a_rotbeta)
    doublebits = "({0} & ~{1} & {2})".format(a_rotbeta, a_rotalpha, rsr(a, 2 * alpha - beta, SUBTERRANEAN_SIZE))
    
    #Check for valid difference
    firstcheck = "({} & ~{})".format(pa, varibits)
    secondcheck = "(BVXOR({}, {}) & {})".format(
        pa, rsr(pa, alpha - beta, SUBTERRANEAN_SIZE), doublebits)
    constraint += ["ASSERT( BVLT({0}, 0bin{1}));".format(a, "1" * SUBTERRANEAN_SIZE) ] # exclude the case that a = 111...111

    constraint += ["ASSERT(({} | {} ) = 0bin{});".format(
        firstcheck, secondcheck, "0" * SUBTERRANEAN_SIZE) ]

    #Assert XORs
    constraint += constraintOfMultiXorForStates([a, pa, a_rotalpha, b], 4)

    #Weight computation
    W = 'W'+str(r)
    constraint += ["ASSERT({0} = BVXOR({1}, {2}) );".format(
                    W, varibits, doublebits)]
    
    return constraint

def zero_vector():
    zero = '0bin'
    for i in range(SUBTERRANEAN_SIZE):
        zero += '0'

    return zero
def one_vector():
    one = '0bin'
    for i in range(SUBTERRANEAN_SIZE):
        one += '1'
    return one

def vector_weight(A, l):
    s = 'BVPLUS( 9, '
    bits = []
    for i in range(l):
        bits.append("0bin00000000@(%s[%d:%d])"%(A, i, i))
    return s + ', '.join(bits) + ' )'

def genObj_activeBits(N):
    # OBJ = ['SUMb', 'SUMv', 'SUMvu']
    terms = []
    for r in range(N):
        W = 'W'+str(r)
        terms.append('0bin00@(%s)' % vector_weight(W, SUBTERRANEAN_SIZE) )
    w_sum = 'BVPLUS( 11, ' + ', '.join(terms) + ')'
    return ["ASSERT( %s = %s );" % ('W', w_sum )]


def constraintOfNontrivial(N):
    a = 'A'+str(0)
    zero = zero_vector()
    return ["ASSERT( NOT( %s = %s ) );" % (a, zero) ]

def subterranean_extract(state, factor):
    value_out = [0 for i in range(OUTPUT_SIZE)]
    # value_out <= extract
    index_j = 1; #print(factor)
    for i in range(OUTPUT_SIZE):
        value_out[i] = state[index_j] ^ state[SUBTERRANEAN_SIZE-index_j]
        index_j = (factor*index_j) % SUBTERRANEAN_SIZE  #97   15^3
    return value_out

def injectionMask(factor):
    list_j = []
    index_j = 1; 
    #print(factor)
    for i in range(OUTPUT_SIZE):
        list_j += [index_j]
        index_j = (factor*index_j) % SUBTERRANEAN_SIZE  
    mask = '0bin'
    for i in range(SUBTERRANEAN_SIZE-1, -1, -1):
        if i in list_j:
            mask += '0'
        else:
            mask += '1'
    return mask

def constraintOfInjection(D, A, Z, factor):
    """d is the diff before extraction
    a is the diff after extraction """
    constraint = []
    constraint.append("ASSERT( %s = BVXOR(%s, %s) );" % (Z, D, A) )
    constraint.append("ASSERT( %s = %s & %s );" % (zero_vector(), Z, injectionMask(factor)) ) 
    return constraint

def constraintOfPassiveEnds(N):
    """the initial and final mask should be zero"""
    constraint  = []
    d0 = 'D'+str(0)
    aN = 'A'+str(N)
    constraint.append("ASSERT( %s = %s );" % (d0, zero_vector() ) )
    constraint.append("ASSERT( %s = %s );" % (aN, zero_vector() ) )
    return constraint

    
def constraintsOfRound(r, base, factor):
    constraints = []
    d0 = 'D'+str(r)    
    z = 'Z'+str(r)
    a = 'A'+str(r)
    pa = 'pA'+str(r)

    # constraints += constraintOfInjection(d0, a, z, factor)

    # except the 1st round, a = d0
    if r != 0:
        constraints += ["ASSERT( %s = %s );" % (a, d0)]
    b = 'B'+str(r)
    constraints += constraintOfChi(a, pa, b, r)
    c = 'C'+str(r)
    constraints += constraintOfTheta(b, c, r)
    d = 'D'+str(r+1)
    constraints += constraintOfPi(c, d, base)
    return constraints

def constraintsOfNRounds(N, base, factor):
    constraints = []
    for r in range(N):
        constraints += constraintsOfRound(r, base, factor)
    d = 'D'+str(N)
    a = 'A'+str(N)
    z = 'Z'+str(N)
    #constraints += constraintOfInjection(d, a, z, factor)
    constraints += ["ASSERT( %s = %s );" % (a, d)]
    constraints += constraintOfNontrivial(N)
    # search the best differential trail, not the zero output
    #constraints += constraintOfPassiveEnds(N)
    constraints += ["ASSERT( %s = %s );" % ('D0', zero_vector())]
    constraints += genObj_activeBits(N)
    #constraints += ["ASSERT( BVLE( W, %s ) );" % int2vector(BOUND)]
    constraints += ["ASSERT( W = %s );" % int2vector(BOUND)]
    constraints += ["QUERY(FALSE);"]
    constraints += ["COUNTEREXAMPLE;"]
    return constraints

def constraintsOfNRounds2(N, base, factor, wt):
    constraints = []
    for r in range(N):
        constraints += constraintsOfRound(r, base, factor)
    d = 'D'+str(N)
    a = 'A'+str(N)
    z = 'Z'+str(N)

    #constraints += constraintOfInjection(d, a, z, factor)

    constraints += ["ASSERT( %s = %s );" % (a, d)]
    constraints += constraintOfNontrivial(N)

    # search the best differential trail, not the zero output
    #constraints += constraintOfPassiveEnds(N)
    
    constraints += ["ASSERT( %s = %s );" % ('D0', zero_vector())]
    constraints += genObj_activeBits(N)

    #constraints += ["ASSERT( BVLE( W, %s ) );" % int2vector(BOUND)]

    constraints += ["ASSERT( W = %s );" % int2vector(wt)]
    constraints += ["QUERY(FALSE);"]
    constraints += ["COUNTEREXAMPLE;"]
    return constraints


def vars_state(s):
    """generate vars of size = lanesize  """
    a = [s+'_'+str(x) for x in range(SUBTERRANEAN_SIZE)] 
    return a

def readFromWord(Dict, name):
    word = Dict[name]
    ret = []
    for i in range(SUBTERRANEAN_SIZE):
        ret.append( (word>>i) & 1 )
    return ret

def get_ActiveExtraction(d, a, Dict, r, factor):
    lines = []
    index_j = 1
    D = readFromWord(Dict, 'D'+str(r))
    A = readFromWord(Dict, 'A'+str(r))
    for i in range(OUTPUT_SIZE):
        if A[index_j]^D[index_j]==1:
            if (A[SUBTERRANEAN_SIZE-index_j]^D[SUBTERRANEAN_SIZE-index_j])==0:
                print("model error!")
            else: 
                s = "z_r%d_%d = %s + %s"%(r,i,a[index_j], a[SUBTERRANEAN_SIZE-index_j])
                lines.append(s)
        index_j = (factor*index_j) % SUBTERRANEAN_SIZE  #193
    return lines

def get_ActiveChi(a, b, Dict, r):
    lines = []
    B = readFromWord(Dict, 'B'+str(r))
    for i in range(SUBTERRANEAN_SIZE):
        if B[i]:
            s = "%s = %s + %s*%s + %s" %(b[i], a[i], a[(i+1)%SUBTERRANEAN_SIZE], a[(i+2)%SUBTERRANEAN_SIZE], a[(i+2)%SUBTERRANEAN_SIZE])
            #s = "%s = %s + %s*%s" %(b[i], a[i], a[(i+1)%SUBTERRANEAN_SIZE], a[(i+2)%SUBTERRANEAN_SIZE])
            lines.append(s)
    return lines
def get_ActiveTheta(b, c, Dict, r):
    lines = []
    C = readFromWord(Dict, 'C'+str(r))
    for i in range(SUBTERRANEAN_SIZE):
        if C[i]:
            lines.append("%s = %s + %s + %s" % (c[i], b[i], b[(i+3)%SUBTERRANEAN_SIZE], b[(i+8)%SUBTERRANEAN_SIZE]))
    return lines    
def get_ActivePi(c, d, a, Dict, r):
    lines = []
    c = Pi(c, BASE)
    D = readFromWord(Dict, 'D'+str(r+1))
    for i in range(SUBTERRANEAN_SIZE):
        if D[i]:
            lines.append("%s = %s" %(a[i], c[i]))       
    return lines
    
def readApprox(filename, N, factor):
    ff = open(filename)
    lines = ff.readlines()
    ff.close()

    Dict = {}
    for line in lines:
        if line.find('ASSERT') != -1:
            ll = line.split(' ')
            Dict[ll[1]] = int(ll[3], 2)
            
    for key in Dict.keys():
        print('{} = {}'.format(key, Dict[key]))
    eq = []
    for r in range(N+1):
        d = vars_state('d_r'+str(r))
        print('r'+str(r)) 
        a = vars_state('a_r'+str(r))
        eq += get_ActiveExtraction(d, a, Dict, r, factor)
        if r < N:
            b = vars_state('b_r'+str(r))
            eq += get_ActiveChi(a, b, Dict, r)
            c = vars_state('c_r'+str(r))
            eq += get_ActiveTheta(b, c, Dict, r)
            d = vars_state('d_r'+str(r+1))
            a = vars_state('a_r'+str(r+1))
            eq += get_ActivePi(c, d, a, Dict, r)
    newName = filename.rstrip('.sol')
    f = open(newName+'eq.txt', 'w')
    for line in eq:
        f.write(line+'\n')
    f.close()  
    Cor = correlationComputer()
    w = Cor.cor_redundant_poly(newName+'eq.txt', 'z')
    return w


def genModel(N, base, factor): # the model for r rounds
    name = 'ST'+ str(SUBTERRANEAN_SIZE)+'_'+str(BOUND)+'_'+str(base)+'.cvc'
    f = open(name, 'w') 
    declare_vars(f)
    constraint = constraintsOfNRounds(N, base, factor)
    for c in constraint:
        f.write(c)
        f.write('\n')
    f.close()
    return 0

def genModel2(N, base, factor, wt): # the model for r rounds
    name = 'ST'+ str(SUBTERRANEAN_SIZE)+'_'+str(BOUND)+'_'+str(base)+'_'+str(wt)+'.cvc'
    f = open(name, 'w')
    declare_vars(f)
    constraint = constraintsOfNRounds2(N, base, factor, wt)
    for c in constraint:
        f.write(c)
        f.write('\n')
    f.close()
    return 0

def RunMultiple(N, start, length): # N rounds, starting position, a bunch of wnd stp files to be generated
    for i in range(start, start+length):
        Base = base_list[i]
        Factor = Base**IND % SUBTERRANEAN_SIZE
        #print(Base, Factor)
        for x in range(21, 31):
            genModel2(N, Base, Factor, x)
            # x for weight
            name = 'ST'+ str(SUBTERRANEAN_SIZE)+'_'+str(BOUND)+'_'+str(Base)+'_'+str(x)
            # add 2>&1 to output time simultaneously
            output = subprocess.check_output('nohup time -p stp '+ name+'.cvc > '+name+'.txt 2>&1 &', shell=True)
            #outstr = bytes.decode(output)
    return 0


if __name__ == '__main__':
    RunMultiple(N, 0, 1)
    
    #genModel(N)
    #readApprox('ST.sol', N, factor)
    #readApprox('ST97_30.sol', N, factor)

