from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler
from itertools import count, repeat
from multiprocessing import Pool, Process, Queue
from Crypto.Util.number import *
import secrets
import time
import random

q = 773659
#q=853
#q=24851
n = 32
k = int(log(q,2) + 1 )
l=4  #len of x

g_v = matrix([2^i for i in range(k)])
I_n = identity_matrix(n)
G = I_n.tensor_product(g_v)
w = G.ncols()  #w=kn

m_bar = 2 * n
m = w + m_bar 
stand_s = sqrt(n) / sqrt(2  * pi)
D = DiscreteGaussianDistributionIntegerSampler(2)
chi = DiscreteGaussianDistributionIntegerSampler(0.002)

#trapdoor door generation
def TrapGen():
    t = [D() for i in range(m_bar * w)]
    R = matrix(ZZ, m_bar, w, t)
    A_bar = random_matrix(Zmod(q), n, m_bar)
    a = G - A_bar * R
    A = A_bar.augment(a)
    T=R.stack(identity_matrix(w))
    return A, T

#U in Z_q(mxn)
def Gen_U(m, n):
    U = []
    for i in range(m):
        U.append(vector(random_matrix(Zmod(q), 1, n)))
    return U    

#x must be int()
def bin_rp(x):
    if x >= 0: 
        a = f"{x:0{k}b}"
        a = list(a)[::-1]   
        return [int(i) for i in a]
    else:
        a = f"{-x:0{k}b}"
        a = list(a)[::-1] 
        return [-int(i) for i in a]
    
#展开位数为k，输出长度为m 用于up_pk 
def bin_rpm(x):
    if x >= 0: 
        a = f"{x:0{k}b}"
        a = list(a)[::-1]   
        ls= [int(i) for i in a]    
        ls+=[0] * (m - k)
        return ls
    
       
def bin_int(list):
    num=0
    for i in range(m):
        num+=list[i]*2^i
    return num  

process = 6
batch = 8
q_v = vector(bin_rp(q))

def O_1(s, c):
    D = DiscreteGaussianDistributionIntegerSampler(sigma = s/2, c = c)
    return D()

def O_2(s, v):
    D = DiscreteGaussianDistributionIntegerSampler(sigma = s)
    return 2 * D() + v

def SampleG(q, u, s):
    u_v = vector(bin_rp(u))
    c   = -(u/q)
    y = O_1(s, c)
    v_v = u_v + y * q_v
    x = []
    for i in range(k-1):
        x_i    = O_2(s, v_v[i])
        x.append(x_i)
        v_v[i+1] = v_v[i+1] + (v_v[i] - x[i])/2
    x.append(v_v[k-1])
    return x

def SampleD(A, u, T):
    D = DiscreteGaussianDistributionIntegerSampler(sigma = 100)
    p = [D() for i in range(A.ncols())]
    p = vector(p)
    v = u - A * p
    allx = []
    for i in v:
        x = SampleG(q, int(i), 1 * sqrt(2))
        allx += x
    x = p + T * vector(allx)
    return x

def sample_range_u(A, U, T):
    r = []
    for u in U:
       x = SampleD(A, u, T)
       r.append(x)
    return r

def SamplePre(A, T, D):
    len_D  = len(D)
    tasks = int(len_D / batch)
    D_split = []
    for i in range(0, len_D, tasks):
        if i == ( batch - 1 )*(tasks):
            D_split.append(D[i:])
            break
        else:
            D_split.append(D[i:i+tasks])
 
    pool = Pool(batch)
    r = pool.starmap(sample_range_u, zip(repeat(A), D_split, repeat(T)))
    pool.close()
    pool.join()
    results = []
    for i in r:
        results += i
    return results


def Steup():
    pp=[]
    for i in range(l):
        pp.append(random_matrix(Zmod(q), n, w))
    pp.append(chi)
    return pp  

def KeyGen():
    D = Gen_U(m, n)
    start = time.time()
    A, T = TrapGen()
    end = time.time()
    print(f"TrapGen: {end - start:.5f}s")
    
    start = time.time()
    R = SamplePre(A, T, D)
    end = time.time()
    print(f"SamplePre: {end - start:.5f}s")

    D = matrix(D).transpose() 
    R = matrix(Zmod(q), R).transpose()
    if A * R != D:
        print("Error")
    else:
        return ([A, -D], [T, R])    

def Encrypt(pp,pk,msg,x=None):
    s = vector(random_matrix(Zmod(q), 1, n))
    e_in = vector([chi() for i in range(m)])
    e_out = vector([chi() for i in range(m)])
    msg_v = vector([int(i) * int(q/2)  for i in msg])
    A,D = pk
    c_in=A.transpose()*s+e_in
    c_out=D.transpose() *s+e_out+msg_v
    
    c_1=(c_in,c_out)
    if x==None:
        return (c_1,None)
    else:
        c_2=[]
        for i in range(l):
            S=matrix([[random.choice([-1, 1]) for j in range(w)] for i in range(m)])
            c_i=((x[i]*G+pp[i]).transpose())*s+(S.transpose())*e_in
            c_2.append(c_i)
        return (c_1,c_2)

def Decrypt(pp,sk,c):
    T,R=sk
    c_1,c_2=c
    c_in,c_out=c_1
    msg_v=c_in*R+c_out
    msg = []
    for i in msg_v:
        if i > int(q/4) and i < int(3*q/4):
            msg.append(1)
        else:
            msg.append(0)
    return msg     

#Decrypt C_re
def Decrypt_re(pp,sk,c):
    T,R=sk
    c_1,c_2=c
    msg_v=c_1*(R.stack(identity_matrix(m)))
    msg = []
    for i in msg_v:
        if i > int(q/4) and i < int(3*q/4):
            msg.append(1)
        else:
            msg.append(0)
    return msg     

def Update_pk(pk):
    U_bar=Gen_U(m, n)
    D_bar=matrix(U_bar).transpose()
    D=pk[1]+D_bar
    return (None,[pk[0],D])


def Update_pk2(pk):
    U_bar=Gen_U(m, n)
    D_bar=matrix(U_bar).transpose()
    up=[]
    for i in range(n):
        for j in range(m):
            bit=bin_rpm(D_bar[i][j].lift())
            up.append(Encrypt(pp,pk,bit)[0])
    D=pk[1]+D_bar
    return (up,[pk[0],D])


def Update_pk3(pk):
    msg = [random.choice([0, 1]) for i in range(m)]
     # formulate Enc(R)
    for i in range(m):
        Encrypt(pp,pk,msg,None)
    
    R=random_matrix(Zmod(q), m, m)
    D=pk[1]
    A=pk[0]
    D_up=D-A*R
    return(R,[A,D_up])

def func_add(x):
    sum=0
    for i in range(l):
        sum+=x[i]
    return sum   

def getx(f):
    while(True):
        x=[random.choice([-1, 1]) for i in range(l)]
        if(f(x)== 0):
            return x

#B_f=B1+B2+...Bl
def Eval(f,x):
    return f(x)

#c_f=c1+c2+...cl
def Eval_c(f,x,B,c):
    return f(c)

def ExtendRight(A,T,U):
    O = zero_matrix(U.ncols(), T.ncols())
    return T.stack(O)

def P2E(E):
    L=[]
    for i in range(k):
        L.append([(2^i)*E])  
    return block_matrix(L)

#v is a vector or list
def BD(v):
    L=[]
    for i in range(len(v)):
        L.append(bin_rp(int(v[i])))
                 
    A=Matrix(L)
    col = []
    for j in range(A.ncols()):
        col.extend(A.column(j))
    return Matrix(col)

def matrixTolist(D):
    D = matrix(D).transpose() 
    return [vector(row) for row in D]

def ReKeyGen(pp,sk_a,pk_a,pk_up,func):
    B_f=Eval(func,pp[:l])
    A_a,D_a = pk_a
    T_a,R_a = sk_a
    A_b,D_b = pk_up
    T_aB = ExtendRight(A_a,T_a,B_f)
    aB = A_a.augment(B_f)
    D=matrixTolist(-D_a)
    R_af = SamplePre(aB, T_aB, D)
    R_af = matrix(Zmod(q), R_af).transpose()
    r_1 = vector(random_matrix(Zmod(q), 1, n))
    e_1 = matrix([chi() for i in range(m)])
    e_2 = matrix([chi() for i in range(m)])
    E_1=matrix([[chi() for j in range(n)] for i in range(k*(k*n+m))])
    E_2=matrix([[chi() for j in range(m)] for i in range(k*(k*n+m))])
    E_3=matrix([[chi() for j in range(m)] for i in range(k*(k*n+m))])
    g=r_1*(A_b.augment(D_b))+vector(e_1.augment(e_2))
    
    S1=E_1*A_b+E_2
    S2=E_1*D_b+E_3+P2E(R_af)
    S3=matrix(m, m, 0)
    S4=identity_matrix(m)  
    Q=block_matrix([[S1, S2], [S3, S4]])
    return (g,Q)

def ReEncrypt(pp,rk,c,x,f):
    c_1,c_2=c
    if(c_2==None or f(x)!=0):
        return "error"
    c_in,c_out=c_1
    c_f=Eval_c(f,x,pp[:l],c_2)
    c_fbar=vector(Matrix(c_in).augment(Matrix(c_f)))
    S=BD(c_fbar).augment(Matrix(c_out))
    g,Q=rk
    a=D()
    ct=a*g+vector(S*Q)
    return (ct,None)

def Update_sk(pk_up,pk,sk):
    T,R=sk
    A,D=pk
    A,D_up=pk_up
    D_bar=D_up-D
    D=matrixTolist(-D_bar)
    R_bar=SamplePre(A, T, D)
    R_bar=matrix(Zmod(q), R_bar).transpose()
    R_up=R_bar+R
    return (T,R_up)

def Update_sk2(up,pk,sk):
    T,R=sk
    A,D=pk
    L=[]
    for i in range(n):
        L2=[]
        for j in range(m):
            pp=None
            msg=Decrypt(pp,sk,(up[i*m+j],None))
            L2.append(bin_int(msg))
        L.append(L2) 
    D_bar=matrix(Zmod(q),L)
    D=matrixTolist(-D_bar)
    R_bar=SamplePre(A, T, D)
    R_bar=matrix(Zmod(q), R_bar).transpose()
    R_up=R_bar+R
    return (T,R_up)


def Update_sk3(up,pk,sk):
    c_in=vector(Zmod(q),m)
    c=([c_in,c_in],None)
    for i in range(m):
        #formulate DEC(R)
        Decrypt(pp,sk,c)
    T,R=sk
    A,D=pk
    return(T,R+up)


#-------------test-----------------------
print(f"n={n},q={q},k={k},m={m}")
start = time.time()
pp=Steup()
end = time.time()
print(f"Steup: {end - start:.5f}s")

start = time.time()
pk_a,sk_a=KeyGen()
end = time.time()
print(f"KeyGen: {end - start:.5f}s")

msg = [random.choice([0, 1]) for i in range(m)]
x=getx(func_add)
start = time.time()
c=Encrypt(pp,pk_a,msg,x)
end = time.time()
print(f"Encrypt: {end - start:.5f}s")

start = time.time()
m1=Decrypt(pp,sk_a,c)
end = time.time()
print(f"Decrypt: {end - start:.5f}s")
# print(m1==msg)

# pk_b,sk_b=KeyGen()
pk_b,sk_b=pk_a,sk_a


start = time.time()
up,pk_up=Update_pk3(pk_b)
end = time.time()
print(f"Update_pk3: {end - start:.5f}s")

start = time.time()
rk=ReKeyGen(pp,sk_a,pk_a,pk_up,func_add) 
end = time.time()
print(f"ReKeyGen: {end - start:.5f}s")

start = time.time()
c_re=ReEncrypt(pp,rk,c,x,func_add)
end = time.time()
print(f"ReEncrypt: {end - start:.5f}s")

start = time.time()
sk_up=Update_sk3(up,pk_b,sk_b)
end = time.time()
print(f"Update_sk3: {end - start:.5f}s")                                                                   