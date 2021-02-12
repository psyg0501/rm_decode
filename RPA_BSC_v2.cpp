// RPA_BSC.cpp : This file contains the 'main' function. Program execution begins and ends there.
//

#include <iostream>
#include <math.h>       // for pow()
#include <cmath>        // for abs()
#include <stdlib.h>     // for srand, rand 
#include <time.h> 
#include <random>       // for uniform distribution
#include <chrono>

using namespace std;


// This fucntion calculates the FHT of a given array F
// The code of this function was taken from the book 'Error Correction Coding: Mathematical Methods and Algorithms' by Todd K. Moon.
// On pg. 383 the function fht.cc is mentioned, which can be downloaded from the webpage: https://www.wiley.com/en-us/Error+Correction+Coding%3A+Mathematical+Methods+and+Algorithms-p-9780471648000 
// in the downloads section.

void fht(int* F, int m)
{
	int i;
	int n;
	int skip, skip2;
	int j, j1, j1skip, k1;
	int tmp;

	n = (1 << m);					// number of points
	skip = 1;
	skip2 = 2;
	for (i = 0; i < m; i++) {		// over each iteration
		j = 0;					// start at the first line
		while (j < n) {
			j1 = j;
			j1skip = j1 + skip;
			for (k1 = 0, j1 = j, j1skip = j1 + skip; k1 < skip; k1++, j1++, j1skip++) {
				tmp = F[j1];
				F[j1] += F[j1skip];
				F[j1skip] = tmp - F[j1skip];
			}
			j += skip2;
		}
		skip = skip2;
		skip2 <<= 1;
	}
}


//This function calculates the v_m_A vector for a given m, a list A and the length of the list A, k
void calculate_v_m_A(int* v_m_A, int m, int A[], int k)
{
	int i, j, prod, n = (int)pow(2.0, m);
	for (i = 0; i < n; i++)
	{
		prod = 1;
		for (j = 0; j < k; j++)
		{
			prod = prod * ((i >> (m - A[j])) % 2);    // '>>' is the bitwise right shift operator
		}
		v_m_A[i] = prod;
	}
	return;
}


//This function calculates the factorial of n
int fact(int n)
{
	if (n == 0)
		return 1;
	return n * fact(n - 1);
}


//This function calculates the number of combinations of n objects taken r at a time.
int nCr(int n, int r)
{
	return (fact(n) / (fact(r) * fact(n - r)));
}


//This function takes an input array arr of length n, and returns an ouput array out of lenght r, having all the 
//r possible combinations of the n objects.
void combinations(int* arr, int n, int r, int** out)
{
	int* idx = new int[r];
	int i, j, k, counter = 0;
	for (i = 0; i < r; i++)
		idx[i] = i;
	for (k = 0; k < r; k++)
	{
		out[counter][k] = arr[idx[k]];
	}
	counter++;
	while (true)
	{
		for (i = r - 1; i >= 0; i--)
		{
			if (idx[i] != i + n - r)
				break;
			else
				continue;
		}
		if (i == -1)
			break;
		idx[i] += 1;
		for (j = i + 1; j < r; j++)
			idx[j] = idx[j - 1] + 1;
		for (k = 0; k < r; k++)
		{
			out[counter][k] = arr[idx[k]];
		}
		counter++;
	}
	delete[] idx;
	return;
}


//This function finds the RM codeword corresponding to a given message array
void RM_codeword(int* codeword, int* info_vec, int m, int r)
{
	int i, j, k, ctr, dim = 0, n = (int)pow(2.0, m);
	int* set_m = new int[m];
	int* v_m_A = new int[n];

	for (i = 0; i < m; i++)
		set_m[i] = i + 1;


	for (i = 0; i <= r; i++)
		dim += nCr(m, i);

	int** basis = new int* [dim];
	for (i = 0; i < dim; i++)
		basis[i] = new int[n];

	for (i = 0; i < n; i++)
		basis[0][i] = 1;
	ctr = 1;

	for (i = 1; i <= r; i++)
	{
		int num_rows = nCr(m, i);
		int** out = new int*[num_rows];
		for (j = 0; j < num_rows; j++)
			out[j] = new int[i];
		combinations(set_m, m, i, out);
		for (k = 0; k < num_rows; k++)
		{
			calculate_v_m_A(v_m_A, m, out[k], i);
			for (j = 0; j < n; j++)
				basis[ctr][j] = v_m_A[j];
			ctr++;
		}
		for (j = 0; j < num_rows; j++)
			delete[] out[j];
		delete[] out;
	}

	for (i = 0; i < n; i++)
		codeword[i] = 0;
	for (i = 0; i < dim; i++)
		for (j = 0; j < n; j++)
			codeword[j] = (codeword[j] + info_vec[i] * basis[i][j]) % 2;

	delete[] set_m;
	delete[] v_m_A;
	for (i = 0; i < dim; i++)
		delete[] basis[i];
	delete[] basis;
	return;
}


//This is the decoder for first-order RM codes
void FHT_decode(int* V, int m)
{
	int i, k, j, ctr, idx, dim, max_elem, temp, r = 1, n = (int)pow(2.0, m);
	int* set_m = new int[m];
	int* v_m_A = new int[n];
	int* bp_rep = new int[n];
	int* abs_vec = new int[n];

	for (i = 0; i < m; i++)
		set_m[i] = i + 1;

	dim = 0;
	for (i = 0; i <= r; i++)
		dim += nCr(m, i);

	int** basis = new int* [dim];
	for (i = 0; i < dim; i++)
		basis[i] = new int[n];

	for (i = 0; i < n; i++)
		basis[0][i] = 1;
	ctr = 1;

	for (i = 1; i <= r; i++)
	{
		int num_rows = nCr(m, i);
		int** out = new int* [num_rows];
		for (j = 0; j < num_rows; j++)
			out[j] = new int[i];
		combinations(set_m, m, i, out);
		for (k = 0; k < num_rows; k++)
		{
			calculate_v_m_A(v_m_A, m, out[k], i);
			for (j = 0; j < n; j++)
				basis[ctr][j] = v_m_A[j];
			ctr++;
		}
		for (j = 0; j < num_rows; j++)
			delete[] out[j];
		delete[] out;
	}

	for (i = 0; i < n; i++)
		bp_rep[i] = (int)pow(-1, V[i]);
	fht(bp_rep, m);
	for (i = 0; i < n; i++)
		abs_vec[i] = abs(bp_rep[i]);
	idx = 0;
	for (i = 0; i < n; i++)
		if (abs_vec[i] > abs_vec[idx])
			idx = i;
	
	//When more than one maximum occurs, randomize the selection of maximum to avoid bias for the all-zero codeword
	int* idx_arr = new int[n];
	ctr = 0;
	for (i = 0; i < n; i++)
	{
		if (abs_vec[i] == abs_vec[idx])
		{
			idx_arr[ctr] = i;
			ctr += 1;
		}
	} 
	if (ctr > 1)
	{
		int rand_num = (rand() % ctr) + 1;    //choose a random number between 1 and ctr
		idx = idx_arr[rand_num - 1];
	}
	delete[] idx_arr;

	max_elem = bp_rep[idx];
	for (i = 0; i < n; i++)
		V[i] = 0;

	ctr = 1;
	if (max_elem > 0)
		for (i = 0; i < m; i++)
		{
			for (j = 0; j < n; j++)
			{
				temp = (idx >> (m - ctr)) % 2;
				V[j] = (V[j] + temp * basis[ctr][j]) % 2;
			}
			ctr++;
		}
	else
	{
		for (k = 0; k < n; k++)
			V[k] = 1;
		for (i = 0; i < m; i++)
		{
			for (j = 0; j < n; j++)
			{
				temp = (idx >> (m - ctr)) % 2;
				V[j] = (V[j] + temp * basis[ctr][j]) % 2;
			}
			ctr++;
		}
	}
	delete[] set_m;
	delete[] v_m_A;
	delete[] bp_rep;
	delete[] abs_vec;
	for (i = 0; i < dim; i++)
		delete[] basis[i];
	delete[] basis;
	return;
}


void RPA_BSC(int* y, int m, int r, int N_max)
{
	int i, j, k, ctr, n = (int)pow(2.0, m), numofchange;
	int* changevote = new int[n];
	int* y_B = new int[n / 2];
	int* y_B_hat = new int[n / 2];
	int* nums = new int[n];
	int B[2];

	for (i = 0; i < N_max; i++)
	{
		for (k = 0; k < n; k++)
			changevote[k] = 0;
		for (j = 1; j < n; j++)
		{
			B[0] = 0;
			B[1] = j;
			ctr = 0;
			for (k = 0; k < n; k++)
				nums[k] = 1;
			for (k = 0; k < n; k++)
			{
				if (nums[k] != 0)
				{
					y_B[ctr] = (y[B[0] ^ k] + y[B[1] ^ k]) % 2;    // '^' is the bitwise XOR operator
					ctr++;
					nums[B[0] ^ k] = 0;
					nums[B[1] ^ k] = 0;
				}
			}
			for (k = 0; k < n / 2; k++)
				y_B_hat[k] = y_B[k];
			if (r == 2)
				FHT_decode(y_B_hat, m - 1);
			else
				RPA_BSC(y_B_hat, m - 1, r - 1, N_max);

			for (k = 0; k < n; k++)
				nums[k] = 1;
			ctr = 0;
			for (k = 0; k < n; k++)
			{
				if (nums[k] != 0)
				{
					if (y_B[ctr] != y_B_hat[ctr])
					{
						changevote[B[0] ^ k] += 1;
						changevote[B[1] ^ k] += 1;
					}
					ctr++;
					nums[B[0] ^ k] = 0;
					nums[B[1] ^ k] = 0;
				}
			}
		}
		numofchange = 0;
		for (j = 0; j < n; j++)
		{
			if (changevote[j] > (n - 1) / 2)
			{
				y[j] = (y[j] + 1) % 2;
				numofchange += 1;
			}
		}
		if (numofchange == 0)
			break;
	}
	delete[] changevote;
	delete[] y_B;
	delete[] y_B_hat;
	delete[] nums;
	return;
}


int main()
{
	int m = 8;
	int r = 2;

	double CrossOverProb[] = { 0.18, 0.185, 0.19, 0.195 };
	int max_codewords = 1000000;

	int i, k, dim, n = (int)pow(2.0,m);
	int N_max = (m + 1) / 2, num_codewords, num_errors;
	int* c = new int[n];
	int* y = new int[n];
	double number, err_prob, p;
	
	/* initialize random seed: */
	srand(time(NULL));
	// construct a trivial random generator engine from a time-based seed:
	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
	std::default_random_engine generator (seed);
	std::uniform_real_distribution<double> distribution(0.0, 1.0);

	dim = 0;
	for (i = 0; i <= r; i++)
		dim += nCr(m, i);

	int* info_vec = new int[dim];

	for (k = 0; k < sizeof(CrossOverProb) / sizeof(double); k++)
	{
		p = CrossOverProb[k];
		num_errors = 0;
		num_codewords = 0;
		while (num_codewords < max_codewords)
		{
		//	for (i = 0; i < dim; i++)
		//		info_vec[i] = rand() % 2;
		//	RM_codeword(c, info_vec, m, r);   // send random codeword
			for (i = 0; i < n; i++)           // send all zeros codeword
				c[i] = 0;
			for (i = 0; i < n; i++)
				y[i] = c[i];
			for (i = 0; i < n; i++)
			{
				number = distribution(generator);
				if (number < p)
					y[i] = (y[i] + 1) % 2;
			}
			RPA_BSC(y, m, r, N_max);
			for (i = 0; i < n; i++)
			{
				if (y[i] != c[i])
				{
					num_errors += 1;
					break;
				}
			}
			num_codewords += 1;
		}
		err_prob = (double)num_errors / (double)num_codewords;
		std::cout << "err_prob = " << scientific << err_prob << "\tat p = " << fixed << p << endl;
	}
	
	
	delete[] y;
	delete[] c;
	delete[] info_vec;

	return 0;
}

// Run program: Ctrl + F5 or Debug > Start Without Debugging menu
// Debug program: F5 or Debug > Start Debugging menu

// Tips for Getting Started: 
//   1. Use the Solution Explorer window to add/manage files
//   2. Use the Team Explorer window to connect to source control
//   3. Use the Output window to see build output and other messages
//   4. Use the Error List window to view errors
//   5. Go to Project > Add New Item to create new code files, or Project > Add Existing Item to add existing code files to the project
//   6. In the future, to open this project again, go to File > Open > Project and select the .sln file
