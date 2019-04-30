# Tools for the Implemention of the Public Key Encryption scheme based on Middle-Produc Learning with Roundings

'''
This sage program includes all necessary tools in order to implement the Public Key Encryption (PKE) scheme from Bai et al. [BBDRLWZ19].

The code consists of the following functions:

*xor*
This function takes as input tho binary strings <k> and <l> of the form "0b101..." or "101..." and computes the xor of them.

*polynomial_from_list*
This function takes as input a list of integers <list_a> and a modulus <q> and constructs a polynomial over <Z/qZ> whose coefficients correspond to <list_a>

*rounding*
The rounding function performs the p-q-rounding for polynomials over <Z_q>. It takes as input a polynomial <a>, the rounding modulus <p> and the general modulus <q>.
It computes the rounded polynomial coefficient-wise.

*cross_rounding*
The cross-rounding function performs a special type of rounding - namely multiplying by <4/q>, rounding and then modulu 2.

*reconciliation*
This is a method used by two parties to agree on a secret bit (the output bit), when they only share a common value up to an approximation factor.
It takes as input two values <y> and <b> and the defining modulus <q> and outputs the agreed bit. For further details see Section 2.2 of [BBDRLWZ19]

*dbl*
This randomized doubling function is required in the case of odd modulus <q>. It takes as input an element <x> of <\Z_q> and returns an elment of <\Z_2q>.

*middle-product*
This function takes as input two polynomials <a> and <b> over the same ring.
The order of the middle-product is defined by <d>, i.e. we multiply <a> times <b> as polynomials and keep only the middle <d> coefficients for their middle-product. The number <k> specifies how many coefficients should be deleted below. For a more detailed introduction of the middle-product see Section 3.1 [RSSS17]

*check_hankel_matrix*
This function checks whether a given polynomial <s> of degree smaller than <n+d-1> has a Hankel matrix of full rank <d>.

*inverting*
This function lifts the input polynomial <a> over <\Z_p> to a polynomial over <\Z_q>.

References:
[BBDRLW19] Shi Bai, Katharina Boudgoust, Dipayan Das, Adeline Roux-Langlois, Weiqianq Wen and Zhenfei Zhang - Middle-Product Learning With Roundings - https://eprint.iacr.org/2019/TODO

[RSSS17] Miruna Rosca and Amin Sakzad and Ron Steinfeld and Damien Stehle - Middle-Product Learning With Errors - https://eprint.iacr.org/2017/628 
'''

import random

# FUNCTION XOR
''' 	INPUT:	- <k> and <l> : two binary strings of the form "0b101..." or "101..." of possibly different length 
	OUTPUT: - The xor of the two binary strings
'''
def xor(k,l):
	# initiating the answer string as an empty string
	ans=""
	# computing the length of the strings assuring the presentation via "0b..."
	len_k=len(bin(int(k,2)))-2
	len_l=len(bin(int(l,2)))-2
	# computing the minimal and maximal length
	len_min=min(len_l,len_k)
	len_max=max(len_l,len_k)
	# computing the string of maximal length
	if len_l>len_k:
		max_str=l
	else:
		max_str=k
	# for the length of the smaller string do a xor
	for i in range(1,len_min+1):
		if l[-i]==k[-i]:
			ans = "0"+ans
		else:
			ans = "1"+ans
	# for the rest of the bigger string copy its entries
	for i in range(len_min+1,len_max+1):
		ans=max_str[-i] + ans
	if len(ans) != len_max:
		print("Oops, there went something wrong.")
	ans=bin(int(ans,2))
	return ans

# FUNCTION POLYNOMIAL_FROM_LIST
'''	INPUT: 	- list of integers <list_a> 
		- modulus <q>
	OUTPUT: - polynomial <tmp> over <Z/qZ> whose coefficients correspond to <list_a>

The list should start with the constant coefficient and end with the coefficient of the leading term.
The variable of the polynomial is 'x' 
'''
def polynomial_from_list(a,q):
	Z=ZZ.quotient(q) 
	P=PolynomialRing(Z,'x')
	x=P.gen()
	tmp=0 
        j=0 
        for i in a: 
		tmp = tmp + (i * (x**(j))) 
		j += 1 
	return tmp

# FUNCTION ROUNDING
''' 	INPUT:	- polynomial <a>
		- rounding modulus <p> 
		- defining modulus <q>
	OUTPUT:	- coefficient of the rounded polynomial \lfloor a * p/q \rceil mod p
		- and the rounded polynomial itself
'''
def rounding(a,p,q):
	a_list=a.list()
	for i in range(len(a_list)):
		#Rounding the polynomial coefficient-wise, then mod p
		a_list[i]=(round(p/q*int(a_list[i])))%p

	#rebuild the polynomial from the list	
	return (a_list,polynomial_from_list(a_list,q))

# FUNCTION CROSS_ROUNDING
''' 	INPUT:	- polynomial <a>
		- defining modulus <q>
	OUTPUT:	- coefficient of the rounded polynomial \lfloor a * 4/q \rceil mod 2
		- and the rounded polynomial itself
'''
def cross_rounding(a,q):
	a_list=a.list()
	for i in range(len(a_list)):
		#Rounding the polynomil coefficient-wise, then mod 2
		a_list[i]=(round((4/q)*int(a_list[i])))%2

	#rebuild the polynomial from the list
	return (a_list,polynomial_from_list(a_list,q))

# FUNCTION RECONCILIATION
''' 	INPUT:	- element <y> of <\Z_q>
		- bit <b>
		- modulus <q>
	OUTPUT:	- the bit computed by the reconciliation mechanism
'''
def reconciliation(y,b,q):
	#for q even
	if q%2==0:
		#define set I_0 - only depending on q
		set_0=[i for i in range(0,round(q/4))]

		#define set I_1 - only depending on q
		set_1=[i for i in range(-floor(q/4),0)]
	
		#define set E - only depending on q
		if q%8==0:
			set_E=[i for i in range(ceil(q/8),q/8)]
		else:
			set_E=[i for i in range(ceil(-q/8),floor(q/8)+1)]
	
		#define set E + I_b - depending on q and b
		if b == 1:
			min_E_b=min(set_E)+min(set_1)
			max_E_b=max(set_E)+max(set_1)
			set_E_b=[i for i in range(min_E_b,max_E_b+1)]	
			if Mod(y,q).lift_centered() in set_E_b:
				return 0
			else:
				return 1

		else:
			min_E_b=min(set_E)+min(set_0)
			max_E_b=max(set_E)+max(set_0)
			i=min_E_b
			set_E_b=[i for i in range(min_E_b,max_E_b+1)]
			if Mod(y,q).lift_centered() in set_E_b:
				return 0
			else:
				return 1
	else:
		print("Oops, there went something wrong. The reconciliation modulus is not even.")
	
# FUNCTION DBL
''' 	INPUT:	- <x> a list of elements of <Z_q>
		- <q> the modulus
	OUTPUT:	- <y> a list of elements of <Z_(2q)>, each the output of the randomized double function
'''
def dbl(x_list,q):
	#random.choice samples from uniform. Thus, put "0" twice in the set to guarantee the required probability distribution
	set_for_e = [-1,0,0,1]
	y=len(x_list)*[0]
	for i in range(len(x_list)):
		e=random.choice(set_for_e)
		y[i]=(2*x_list[i]-e)%(2*q)
	#rebuild the polynomial from the list
	return polynomial_from_list(y,q)

# FUNCTION MIDDLE-PRODUCT
''' 	INPUT:	- <a> and <b> : polynomials to middle-multiply
		- <d> : number of coefficients to preserve
		- <k> : number of coefficients to delete below and upper bound to delete on top
	OUTPUT: - The middle-product of <a> and <b> of width <d> over <Z/qZ>
'''
def middleproduct(a,b,d,k,q): 
	if a.parent() != b.parent():
		print("Oops, there is a problem: Your two polynomials don't have the same parent ring.")
	P=a.parent()	
	x=P.gen()
	# first compute the full product of a and b modulo x^(k+d) modulo q
        m=(a*b)%x^(k+d)
        # safe the coefficients
        m_list=m.list() 
        # deleting coefficients underneath
        for i in range(k):
                del m_list[0]
               
	# rebuild the polynomial from the list	
	return polynomial_from_list(m_list,q)

# FUNCTION CHECK_HANKEL_MATRIX
''' 	INPUT:	- <s> polynomial of degree smaller than <d+n-1>
		- <d> : number of rows of the Hankel matrix
		- <n> : number of columns of the Hankel matrix
	OUTPUT: - Boolian value depending if the corresponding Hankel matrix has full rank or not
'''
def check_hankel_matrix(s,d,n):
	s_1=[s.list()[i] for i in range(0,n)]
	s_2=[s.list()[i] for i in range(n,n+d-1)]
	if s_1 + s_2 != s.list():
		print("Ooops, there went something wrong.")
	if matrix.hankel(s_1,s_2).rank() == d: #ONLY WORKS OVER FIELDS! 
		return True
	else:
		return False 

# FUNCTION INVERTING
''' 	INPUT:	- <a> : polynomial to lift from <\Z_p> to <\Z_(q)>
		- <p> : rounding modulus
		- <q> : general modlulus
	OUTPUT: - liftet polynomial, now an element ovor <\Z_q>
'''
def inverting(a,p,q):
	a_list=a.list()
	for j in range(len(a_list)):
		#set of possible elements
		set_invert=[]
		for i in range(q): #very slowly ?
			if (round(i*(p/q))%p)==a_list[j]:
				set_invert.append(i)
		a_list[j]=random.choice(set_invert)
	return polynomial_from_list(a_list,q)
