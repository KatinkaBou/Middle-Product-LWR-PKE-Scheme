# Public Key Encryption scheme based on Middle-Produc Learning with Roundings

'''
UPDATE 30.04.2019 !! The work is still in progress !! It is not correctly implemented right now !! 

This is a sage program realizing the Public Key Encryption (PKE) scheme from Bai et al. [BBDRLWZ19].
The PKE scheme is chosen to be IND-CPA secure under the Middle-Product Computational Learning With Roundings (MP-CLWR) problem using appropriate parameters.

The code consists of the following functions:

*setparams*
This function takes as input the security parameter <sec_lambda> and computes the parameters of the PKE scheme corresponding to the examples parameters given by the authors of [BBDRLWZ19] in Section %TODO.

*keygen*
This function computes a public key for the PKE scheme corresponding to the security parameter <sec_lambda>.

*encrypt*
This function takes as input the security parameter <sec_lambda> and computes the ciphertext <(c_1,c_2)> for the message <m> under the public key <pk>.

*decrypt*
This function takes as input the security parameter <sec_lambda> and decrypts the ciphertext <c> given the secret key <sk>.

References:
[BBDRLW19] Shi Bai, Katharina Boudgoust, Dipayan Das, Adeline Roux-Langlois, Weiqianq Wen and Zhenfei Zhang - Middle-Product Learning With Roundings - https://eprint.iacr.org/2019/TODO
'''

import random
from Crypto.Hash import MD5
load("tools.sage")

# FUNCTION SETPARAMS
''' 	INPUT:	- <sec_lambda> : security parameter for the PKE scheme
	OUTPUT: - <n> : the dimension, should be even
		- <q> : the modulus
		- <p> : the rounding modulus
		- <t> : the number of MP-LWE samples
		- <Z> : the quotient ring Z/qZ
		- <P> : the polynomial ring over <Z> in the variable <x>
		- <x> : the variable of <P>
'''
@cached_function
def setparams(sec_lambda):
	if sec_lambda%2 == 0:
		n=sec_lambda
	else: 
		n=sec_lambda+1
	q=next_prime(round(n^3*log(n)^(1/2)))
	t=round(log(n))
	p=round(n*log(n))
	Z=ZZ.quotient(q) 
	P=PolynomialRing(Z,'x')
	x=P.gen()
	return (n,q,t,p,Z,P,x)

# FUNCTION KEYGEN
''' 	INPUT:	- <sec_lambda> : security parameter for the PKE scheme
	OUTPUT: - the secret key <sk> and the public key <pk> of the PKE scheme 
'''
def keygenmp(sec_lambda):
	# initialize the parameters
	(n,q,t,p,Z,P,x)=setparams(sec_lambda)
	# initialize the public key
	pk=[]
	#sample private key having a hankel matrix of full rank n, here d=k=n/2
	s=P.random_element(2*n-2)
	while check_hankel_matrix(s,n,n) == False:
		s=P.random_element(2*n-2)
    	sk=s

    	for i in range(t):
        	#choose random first part of public key a
		a=P.random_element(n-1)
      		# calculate mp of a and s
        	m=middleproduct(a,s,n,n-1,q)
		# round the middle-product
		b=rounding(m,p,q)[1]
		pk.append((a,b))
    	return (sk,pk)

# FUNCTION ENCRYPT
''' 	INPUT:	- public key <pk> of the form <(a_i,b_i)_{i \leq t}> and 
		- message <m> a list of <n/2> binary entries
	OUTPUT: - ciphertext <c_1,c_2,c_3> corresponding to the public key <pk> and the message <m>
'''
def encrypt(pk,m,sec_lambda):
	# initialize the parameters
        (n,q,t,p,Z,P,x)=setparams(sec_lambda)
	#put initial value of c_1 (first ciphertext part) and c_1 and v (for the second ciphertext part)
	c_1=0
	c_2=0
	v=0
	for i in range(t):
		#choose random binary r
		list_r=[ZZ.random_element(0,2) for j in range(n/2+1)]
		r=polynomial_from_list(list_r,q)	
		c_1=c_1+r*pk[i][0]
		v=v+middleproduct(r,inverting(pk[i][1],p,q),n/2,n/2,q)
	#for q even
	if q%2==0:
		c_2=cross_rounding(v,q)[0]	
		k="".join(map(str,rounding(v,2,q)[0]))
		k=bin(int(k,2))
		print("This is k ",k)
		hash=MD5.new(k)
		print("This is hash of k ",hash.hexdigest())
		k1=bin(int(hash.hexdigest(),16))
		print("This is the binary string of the hash of k ",k1)
		m1=bin(int("".join(map(str,m)),2))
		print("This is the binary string of the message ",m1)
		c_3=xor(m1,k1)	
		print("This is the xor of the massage with the hash value ",c_3)
		c_3=[int(c_3[i],2) for i in range(len(c_3))] 
	#for q odd we need the use of the randomized doubling function <dbl>
	else:
		list_v=[int(x) for x in v.list()]
		c_2=cross_rounding(dbl(list_v,q),2*q)[0]
		k="".join(map(str,rounding(dbl(list_v,q),2,2*q)[0]))
		k=bin(int(k,2))
		print("This is k ",k)
		hash=MD5.new(k)
		print("This is hash of k ",hash.hexdigest())
		k1=bin(int(hash.hexdigest(),16))
		print("This is the binary string of the hash of k ",k1)
		m1=bin(int("".join(map(str,m)),2))
		print("This is the binary string of the message ",m1)
		c_3=xor(m1,k1)	
		print("This is the xor of the massage with the hash value ",c_3)	
	return (c_1,c_2,c_3)

# FUNCTION DECRYPT
''' 	INPUT:	
	OUTPUT: 
'''
def decrypt(ciphertext,sk,sec_lambda):
	# initialize the parameters
        (n,q,t,p,Z,P,x)=setparams(sec_lambda)

	w=middleproduct(ciphertext[0],sk,n/2,((3*n)/2)-1,q)
	coeff=w.list()
	if len(coeff) == len(ciphertext[1]):
		res=len(coeff)*[0]
		print("c_2 and w have the same length")
		for i in range(len(coeff)):
			if q%2==0:
				res[i]=reconciliation(coeff[i],ciphertext[1][i],q)
			else:
				res[i]=reconciliation(coeff[i]*2,ciphertext[1][i],2*q)
		print("This is Rec(w,c_2)",res, "of lenght",len(res))
		res_str="".join(map(str,res))
		hash=MD5.new(res_str)
		print("This is hash of Rec(w,c_2)",hash)
		k1=bin(int(hash.hexdigest(),16))
		print("This is the binary string of the hash of Rec(w,c_2 ",k1)
		ans=xor(k1,ciphertext[2])
	else:
		print("Mhhh, c_2 and w do not have the same length.")
		
	return ans
