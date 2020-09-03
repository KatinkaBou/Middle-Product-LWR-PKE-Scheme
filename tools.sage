# -*- coding: utf-8 -*-
"""
    Created on 09/03/2020
    Last Modification 09/03/2020
    
    @creator: Katharina BOUDGOUST
    
    ####################
    #   Needed Tools   #
    ####################

"""

'''
This sage program includes all necessary tools in order to implement the Public Key Encryption (PKE) scheme from Bai et al. [BBDRLWZ19].

The code consists of the following functions:

*round2*
This function takes as input a float <f> that should be rounded to the nearest integer. The sage rounding function <round()> rounds <4.5> to <5> but <-4.5> to <-5>. 
In order to guarantee the correctness of the implementation (e.g. reconciliation mechanism), we define our own rounding function <round2()> ensuring that <-4.5> is rounded to <-4>.

*xor*
This function takes as input two binary strings <k> and <l> of the form "0b101..." or "101..." and computes the xor of them. The two strings don't have to be of the same length.

*polynomial_from_list*
This function takes as input a list of integers <list_a> and a modulus <q> and constructs a polynomial over <Z/qZ> whose coefficients correspond to <list_a>.

*rounding*
The rounding function performs the p-q-rounding for polynomials over <Z/qZ> coefficient-wise. It takes as input a polynomial <a>, the rounding modulus <p> and the general modulus <q>.
It computes the rounded polynomial coefficient-wise.

*cross_rounding*
The cross-rounding function performs a special type of rounding - namely multiplying by <4/q>, rounding and then modulo 2.

*reconciliation*
This is a method used by two parties to agree on a secret bit (the output bit), when they only share a common value up to an approximation factor.
It takes as input two values <y> and <b> and the defining modulus <q> and outputs the bit on which they agreed beforehand. For further details see Section 2.2 of [BBDRLWZ19] and the original description of the reconciliation mechanism in [Pei14].

*dbl*
This randomized doubling function is required in the case of odd modulus <q> in order to ensure that the reconciliation mechanism does not output a biased bit. It takes as input an element <x> of <Z/qZ> and returns an elment of <Z/2qZ>.

*middle-product*
This function takes as input two polynomials <a> and <b> over the same ring.
The order of the middle-product is defined by <d>, i.e., we multiply <a> times <b> as polynomials and keep only the middle <d> coefficients for their middle-product. The number <k> specifies how many coefficients should be deleted below. For a more detailed introduction of the middle-product see Section 3.1 [RSSS17].

*check_hankel_matrix*
This function checks whether a given polynomial <s> of degree smaller than <n+d-1> has a Hankel matrix of order <dxn> of full rank <d>.

*inverting*
This function lifts the input polynomial <a> over <Z/pZ> to a polynomial over <Z/qZ>. In order to do so, the function deterministically lifts each coefficient <c> of the input polynomial <a> to <Z/qZ> by multiplying it with <q/p>, then rounding it. Afterwards, the function iteratively computes all elements that are rounded to <c> and chooses one of them uniformly at random.

References:
[BBDRLW19] Shi Bai, Katharina Boudgoust, Dipayan Das, Adeline Roux-Langlois, Weiqianq Wen and Zhenfei Zhang - Middle-Product Learning with Rounding Problem and its Applications - https://eprint.iacr.org/2019/TODO

[Pei14] Chris Peikert - Lattice cryptography for the internet - https://eprint.iacr.org/2014/070

[RSSS17] Miruna Rosca and Amin Sakzad and Ron Steinfeld and Damien Stehle - Middle-Product Learning With Errors - https://eprint.iacr.org/2017/628 
'''

import random

# FUNCTION ROUND2
''' 	INPUT: 	- a float <f>
	OUTPUT:	- the integer nearest to <f> (in the case of -0.5, it's rounding up)
'''
def round2(f):
	if f<0 and (f-round(f)==0.5): 
		return ceil(f)
	else:
		return round(f)
		

# FUNCTION XOR
''' 	INPUT:	- <k> and <l> : two binary strings of the form "0b101..." or "101..." of possibly different length 
	OUTPUT: - The xor of the two binary strings in the form "0b110..."
'''
def xor(k,l):
	# initiating the answer string as an empty string
	ans=""
	# computing the length of the strings assuring the presentation via "0b...", thus we have to substract 2
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
	# for the length of the smaller string do a xor (from the left to the right)
	for i in range(1,len_min+1):
		if l[-i]==k[-i]:
			ans = "0"+ans
		else:
			ans = "1"+ans
	# for the rest of the bigger string copy its entries
	for i in range(len_min+1,len_max+1):
		ans=max_str[-i] + ans
	if len(ans) != len_max:
		print("Oops, something went wrong.")
	ans=bin(int(ans,2))
	return ans

# FUNCTION POLYNOMIAL_FROM_LIST
'''	INPUT: 	- list of integers <list_a> 
		- modulus <q>
	OUTPUT: - polynomial <tmp> over <Z/qZ> whose coefficients correspond to <list_a>

The list should start with the constant coefficient and end with the coefficient of the leading term.
The variable of the polynomial is 'x'.
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
	OUTPUT:	- coefficient list of the rounded polynomial <round(a*p/q)%p>
		- and the rounded polynomial itself
'''
def rounding(a,p,q):
	# this step is necessary is the entries of <a.list()> can't be reassigned
	a_list=a.list()
	for i in range(len(a_list)):
		# rounding the polynomial coefficient-wise, then mod p
		a_list[i]=(round2(p/q*int(a_list[i])))%p

	# rebuild the polynomial from the list	
	return (a_list,polynomial_from_list(a_list,q))

# FUNCTION CROSS_ROUNDING
''' 	INPUT:	- polynomial <a>
		- defining modulus <q>
	OUTPUT:	- coefficient list of the rounded polynomial <floor(a*4/q)%2>
		- and the rounded polynomial itself
'''
def cross_rounding(a,q):
	# this step is necessary is the entries of <a.list()> can't be reassigned
	a_list=a.list()
	for i in range(len(a_list)):
		# floor rounding the polynomil coefficient-wise, then mod 2
		a_list[i]=(floor((4/q)*int(a_list[i])))%2

	# rebuild the polynomial from the list
	return (a_list,polynomial_from_list(a_list,q))

# FUNCTION RECONCILIATION
''' 	INPUT:	- element <y> of <Z/qZ>
		- bit <b>
		- modulus <q>
	OUTPUT:	- the bit computed by the reconciliation mechanism
'''
def reconciliation(y,b,q):
	# using the notation from [Pei14]
	# for q even
	if q%2==0:
		# define set I_0 - only depending on q
		set_0=[i for i in range(0,round2(q/4))]

		# define set I_1 - only depending on q
		set_1=[i for i in range(-floor(q/4),0)]
	
		# define set E - only depending on q
		if q%8==0:
			set_E=[i for i in range(-q/8,q/8)]
		else:
			set_E=[i for i in range(ceil(-q/8),floor(q/8)+1)]
	
		# define set E + I_b - depending on q and b
		# note that E and I_0 are intervalls intersecting with <Z>
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
			set_E_b=[i for i in range(min_E_b,max_E_b+1)]
			if Mod(y,q).lift_centered() in set_E_b:
				return 0
			else:
				return 1
	else:
		print("Oops, something went wrong. The reconciliation modulus is not even.")
	
# FUNCTION DBL
''' 	INPUT:	- <x_list> a list of elements of <Z/qZ>
		- <q> the defining modulus
	OUTPUT:	- <y> a list of elements of <Z/2qZ>, each the output of the randomized double function
'''
def dbl(x_list,q):
	# the function random.choice() samples from uniform. Thus, we put "0" twice in the set to guarantee the required probability distribution
	set_for_e = [-1,0,0,1]
	y=len(x_list)*[0]
	for i in range(len(x_list)):
		e=random.choice(set_for_e)
		y[i]=(2*x_list[i]-e)%(2*q)
	# rebuild the polynomial from the list
	return polynomial_from_list(y,2*q) 

# FUNCTION MIDDLE-PRODUCT
''' 	INPUT:	- <a> and <b> : polynomials to middle-multiply
		- <d> : number of coefficients to preserve
		- <k> : number of coefficients to delete below and upper bound to delete on top
		- <q> : the defining modulus
	OUTPUT: - The middle-product of <a> and <b> of width <d> over <Z/qZ>
'''
def middleproduct(a,b,d,k,q): 
	if a.parent() != b.parent():
		print("Oops, there is a problem: Your two polynomials don't have the same parent ring.")
	P=a.parent()	
	x=P.gen()
	# first compute the full product of a and b modulo x^(k+d) modulo q
        m=((a*b)%x^(k+d))
        # register the coefficients
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
	# divide the list of coefficients of the input polynomial <s> into two lists corresponding to the defining row and defining column of the Hankel matrix
	s_1=[s.list()[i] for i in range(0,n)]
	s_2=[s.list()[i] for i in range(n,n+d-1)]
	if s_1 + s_2 != s.list():
		print("Ooops, something went wrong.")
	if matrix.hankel(s_1,s_2).rank() == d: #ONLY WORKS OVER FIELDS! --> q prime
		return True
	else:
		return False 

# FUNCTION INVERTING
''' 	INPUT:	- <a> : polynomial to lift from <Z/pZ> to <Z/qZ>
		- <p> : rounding modulus
		- <q> : general modulus
	OUTPUT: - liftet polynomial, now an element over <Z/qZ>
'''
def inverting(a,p,q):
	# resgister the coefficients of the polynomial <a> in a list
	a_list=a.list()
	for j in range(len(a_list)):
		# deterministically lift the coefficient to an element in <Z/qZ>
		y=round2(int(a_list[j])*q/p)
		list_temp=[y]
		# walk to the right of the "rounding circle"
		i=1
		while (round2((y+i)*p/q)%p)==(round2(y*p/q)%p):
			list_temp.append(int(y+i))
			i=i+1
		# walk to the left of the "rounding circle"
		k=1
		while (round2((y-k)*p/q)%p)==(round2(y*p/q)%p):
			list_temp.append(y-k)
			k=k+1
		a_list[j]=random.choice(list_temp)
	return polynomial_from_list(a_list,q)
