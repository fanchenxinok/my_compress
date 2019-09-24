#include <iostream>
#include <time.h>
#include <sys/stat.h>
using namespace std;

inline void Swap(int &a, int &b)
{
	int c = a;
	a = b;
	b = c;
	return;
}

inline void Print(int *pIn, int m)
{
	if(!pIn || m <= 0) return;
	int i = 0;
	for(; i < m; i++){
		cout << pIn[i] << " ";
	}
	cout << endl;
	return;
}

/* 随机生成 [0, m) 的数到pOut, 不能重复 */
void RandM(int *pOut, int m)
{
	if(!pOut || m <= 0) return;
	
	int i = 0;
	for(; i < m; i++){
		pOut[i] = i;
	}

	srand(time(NULL) + rand());
	i = m;
	while(i > 0){
		int randIdx = rand() % i;
		Swap(pOut[--i], pOut[randIdx]);
	}
	return;
}

/* 随机生成 [0, n) 中的 m 个不重复的数 */
void RandM_N(int *pOut, int m, int n)
{
	if(!pOut || m <= 0 || m > n) return;
	
	int *pTmp = new int[n]();
	int i = 0, j = 0;
	for(; i < n; i++){
		pTmp[i] = i;
	}

	srand(time(NULL) + rand());
	i = n;
	while(j < m){
		int randIdx = rand() % i;
		pOut[j++] = pTmp[randIdx];
		Swap(pTmp[--i], pTmp[randIdx]);
	}

	delete [] pTmp;
	pTmp = NULL;
	return;
}

#define BITS (32)
#define MASK (0x1f)
#define SHIFT (5)

inline void setBit(int *pMap, int bit)
{
	if(!pMap || bit <= 0) return;
	pMap[bit >> SHIFT] |= (1 << (bit & MASK));
	return;
}

inline int tstBit(int *pMap, int bit)
{
	if(!pMap || bit <= 0) return 0;
	return pMap[bit >> SHIFT] & (1 << (bit & MASK));
}

/* 随机生成 [0, n) 中的 m 个不重复的数 */
void RandM_N2(int *pOut, int m, int n)
{
	if(!pOut || m <= 0 || m > n) return;
	
	int *pMap = new int[(n >> SHIFT) + 1]();
	int i = 1;
	for(; i <= n; i++){
		setBit(pMap, i);
	}

	srand(time(NULL) + rand());
	i = 0;
	while(i < m){
		int randIdx = rand() % n;
		if(tstBit(pMap, randIdx+1) != 1){
			continue;
		}
		pOut[i++] = randIdx;
	}

	delete [] pMap;
	pMap = NULL;
	return;
}

/* return ms */
int my_calc_process_time(int *pStartMs)
{
	clock_t endTime = clock();
	if(pStartMs){
		return endTime - *pStartMs;
	}
	return endTime;
}

int main()
{
	int *pRand = new int[100]();

	int ms = 0;
	ms = my_calc_process_time(NULL);
	RandM(pRand, 100);
	ms = my_calc_process_time(&ms);
	cout << "(1) spend time: " << ms << " ms" << endl;
	Print(pRand, 100);

	ms = my_calc_process_time(NULL);
	RandM_N(pRand, 1000, 100000);
	ms = my_calc_process_time(&ms);
	cout << "(2) spend time: " << ms << " ms" << endl;
	//Print(pRand, 10000);

	ms = my_calc_process_time(NULL);
	RandM_N2(pRand, 1000, 100000);
	ms = my_calc_process_time(&ms);
	cout << "(3) spend time: " << ms << " ms" << endl;
	//Print(pRand, 100);

	delete [] pRand;
	pRand = NULL;
	return 0;
}