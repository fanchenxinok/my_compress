/**********************************************
Autor: fanchenxin
***********************************************/
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <stack>
#include <vector>
#include <map>
#include <bitset>
#include <string.h>
#include <getopt.h>
#include <unistd.h>
#include <stdarg.h> 
#include <time.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>
using namespace std;

#define LOG_LEVEL (1)
#define NEED_DUMP_DATA (0)

#if LOG_LEVEL != 0
#if LOG_LEVEL == 1
#define my_printf
#define my_warning
#define my_error(msg, ...) printf("\033[1;31;43m" msg "\033[0m\n", ##__VA_ARGS__)
#elif LOG_LEVEL == 2
#define my_printf
#define my_warning (printf)
#define my_error(msg, ...) printf("\033[1;31;43m" msg "\033[0m\n", ##__VA_ARGS__)
#else
#define my_printf (printf)
#define my_warning (printf)
#define my_error(msg, ...) printf("\033[1;31;43m" msg "\033[0m\n", ##__VA_ARGS__)
#endif

#else
#define my_printf
#define my_warning
#define my_error
#endif

typedef char Int8;
typedef short Int16;
typedef int Int32;

typedef unsigned char uInt8;
typedef unsigned short uInt16;
typedef unsigned int uInt32;

/* 取得v 的低n 位 */
#define GET_BITS(v, n) ((unsigned)v & ((1U << (n)) - 1))
/* 取余运算 */
#if 1
#define GET_MOD(a, b) ((a) % (b))
#else
#define GET_MOD(a, b) ((a) & (b - 1)) //这种写法b必须是2的整数倍
#endif

#define CHECK_POINTER_NULL(pointer, retValue) \
	do{ \
		if(pointer == NULL){ \
			printf("Fatal error: malloc %s Fail !!!!\n", #pointer); \
			return retValue; \
		} \
	}while(0)

/* 可变参数为前面分配的数组资源
  (不可用于释放类资源，因为delete void* 不会
  调用类的析构函数) */
inline void ASSERT_RELEASE(void *pointer, ...) 
{ 
	if(pointer == NULL){
		printf("Fatal error:  pointer is NULL !!!!\n"); 
		uInt32 argNum = 0;
		va_list argp;
		va_start(argp, pointer);
		while (1){
			void *arg = va_arg(argp, void*);
			if(arg == NULL) 
				break; 
			delete [] arg;
			arg = NULL;
			argNum++;
		}
		va_end(argp);
		printf("Parameter Num = %d \n", argNum);
		exit(-1);
	}
	return;
}

typedef enum
{
	FALSE = 0,
	TRUE = 1
}enBool;

#pragma pack (1)
typedef struct
{
	Int8   cmp_head_code[4];  //文件头识别码
	uInt32 cmp_before_bytes;  //压缩前的字节数
	uInt16 block_num;  //块个数(每块1M)
	//uInt32 cmp_after_bytes;   //压缩后的字节数(不包括该文件头的大小)
}stCmpFileHead;
#pragma pack ()

static stCmpFileHead fileHeadInfo = {'F','C','X','0',0};

#define BLOCK_BYTES (1024*1024) // 1M

template <typename T>
static void my_swap(T &a, T &b)
{
	T p = a;
	a = b;
	b = p;
}

template <typename T>
static void print(T* arry, uInt32 num)
{
	uInt32 i;
	for(i = 0; i < num; i++)
		printf("%c ", arry[i]);
	cout << endl;
}

/*************************************************
编程珠玑里bitMap的实现:
	用bit 存储数字比如:
	{1, 5, 8} 用bit 存储为:  0 1 0 0 0 1 0 0 1
**************************************************/
#define BIT_SHIFT_8   (3)
#define BIT_MASK_8    (0x07)

#define BIT_SHIFT_32 (5)
#define BIT_MASK_32  (0x1f)
/* 设置num 位的bit 为1 */
static void setBit_uInt8(uInt8 *pBitMap, uInt32 num)
{
	if(!pBitMap)
		return;
	pBitMap[num >> BIT_SHIFT_8] |= (1 << (num & BIT_MASK_8));
	return;
}

/* 设置num 为的bit 为0 */
static void clrBit_uInt8(uInt8 *pBitMap, uInt32 num)
{
	if(!pBitMap)
		return;
	pBitMap[num >> BIT_SHIFT_8] &= ~(1 << (num & BIT_MASK_8));
	return;
}

/* 检验num 位的bit 是否为1 */
static enBool tstBit_uInt8(uInt8 *pBitMap, uInt32 num)
{
	if(!pBitMap)
		return FALSE;
	if(pBitMap[num >> BIT_SHIFT_8] & (1 << (num & BIT_MASK_8)))
		return TRUE;
	else
		return FALSE;
}

/* 设置num 位的bit 为1 */
static void setBit_uInt32(uInt32 *pBitMap, uInt32 num)
{
	if(!pBitMap)
		return;
	pBitMap[num >> BIT_SHIFT_32] |= (1 << (num & BIT_MASK_32));
	return;
}

/* 设置num 为的bit 为0 */
static void clrBit_uInt32(uInt32 *pBitMap, uInt32 num)
{
	if(!pBitMap)
		return;
	pBitMap[num >> BIT_SHIFT_32] &= ~(1 << (num & BIT_MASK_32));
	return;
}

/* 检验num 位的bit 是否为1 */
static enBool tstBit_uInt32(uInt32 *pBitMap, uInt32 num)
{
	if(!pBitMap){
		return FALSE;
	}
	if(pBitMap[num >> BIT_SHIFT_32] & (1 << (num & BIT_MASK_32))){
		return TRUE;
	}else{
		return FALSE;
	}
}
/**************************************************
Golomb-Rice是Golomb编码的一个变种，
它给Golomb编码的参数m添加了个限制条件：
	m必须是2的次幂。这样有两个好处：

    不需要做模运算即可得到余数r，r = N & (m - 1)
    对余数r编码更为简单，只需要取r二进制的低log2(m)

    位即可。

则Golomb-Rice的编码过程更为简洁：

    初始化参数m，m必须为2的次幂
    计算q和r，q = N / m ; r = N & (m - 1)
    使用一元编码编码q
    取r的二进制位的低log2(m)位作为r的码字。

    编码后的样子:  1 1 1...(q个) + 0 + r (低log2(m)位)

***************************************************/

#define BIT_NUMS (32)
#define M (4)
#define Q_BITS (2) /* 2 ^ Q_BITS = M */

void golomb_set_bit(
	bitset<BIT_NUMS> *pBitBuf,
	uInt32 qLen, 
	uInt32 curPos,
	uInt8 &curBitPos,
	uInt32 &rVal)
{
	//cout << "(" << curPos << ")";
	if(curPos < qLen){
		pBitBuf->set(curBitPos++); //set 1
		//cout << " " << 1;
	}
	else if(curPos == qLen){
		pBitBuf->reset(curBitPos++); //set 0
		//cout << " " << 0;
	}
	else{
		uInt8 bit = rVal & 0x01;
		if(bit == 0x01){
			pBitBuf->set(curBitPos++); //set 1
			//cout << " " << 1;
		}
		else{
			pBitBuf->reset(curBitPos++); //set 0
			//cout << " " << 0;
		}
		rVal >>= 1;
	}
	return;
}

/* Golomb-Rice 编码:  num -> bits */
void golomb_rice_encode(vector<uInt32> &in, vector<uInt32> &out)
{
	bitset<BIT_NUMS> bitBuf;
	bitBuf.reset();
	uInt8 curBitPos = 0;
	
	bitset<BIT_NUMS> *pCurBitBuf = &bitBuf;
	uInt32 i = 0;
	for(; i < in.size(); i++){
		uInt32 q = in[i] >> Q_BITS;
		uInt32 r = in[i] & (M - 1); // r = in[i] % M ，M必须是2的倍数
		uInt32 len = q + 1 + Q_BITS;
		//printf("\n(%d) Val=%d, q=%d, r=%d, len=%d\n", i, in[i], q, r, len);
		uInt32 j = 0;
		for(; j < len; j++){
			uInt8 leftLen = BIT_NUMS - curBitPos;
			if(leftLen < len){ /* 如果剩余的bit 位不够存储 */
				uInt8 k = 0;
				for(; j < len && k < leftLen; k++, j++){ /* 将剩余的bit 位填满 */
					golomb_set_bit(pCurBitBuf, q, j, curBitPos, r);
				}
				j -= 1;

				if(k >= leftLen){
					//cout << endl;
					//cout << "encodeBits = " << *pCurBitBuf << endl;
					out.push_back(pCurBitBuf->to_ulong());
					curBitPos = 0;
					pCurBitBuf->reset();
				}
			}
			else{
				golomb_set_bit(pCurBitBuf, q, j, curBitPos, r);
			}
		}
	}

	if(curBitPos != 0){
		//cout << endl;
		//cout << "encodeBits = " << *pCurBitBuf << endl;
		uInt32 encodeVal = pCurBitBuf->to_ulong();
		out.push_back(encodeVal);
		curBitPos = 0;
		pCurBitBuf->reset();
	}
	return;
}

/* Golomb-Rice 解码: bits -> num 
    needOutNum: 需要解码的个数，用来结束判断
*/
void golomb_rice_decode(vector<uInt32> &in, vector<uInt32> &out, uInt32 needOutNum)
{
	uInt32 i = 0, zeroCnt = 0;
	uInt32 q = 0, r = 0, rBitCnt = 0;
	/*标记是否是q 个1和r之间的分隔bit 0 之前还是之后*/
	enBool bSeperatorAfter = FALSE; 
	for(; i < in.size(); i++){
		//printf("in[%d] = %x\n", i, in[i]);
		uInt8 curPos = 0;
		for(; curPos < BIT_NUMS; curPos++){
			uInt8 bit = in[i] & 0x01;
			//my_printf("%d ", bit);
			if(bSeperatorAfter == FALSE && bit == 1){ // 0分隔符之前的1的个数就是q的值
				q++;
				zeroCnt = 0;
			}
			else if(bSeperatorAfter == FALSE && bit == 0){ // if bit == 0 && bSeperatorAfter == FALSE
				bSeperatorAfter = TRUE;
				zeroCnt++;
				//if(zeroCnt > (Q_BITS + 1))
				//	return;
			}
			else{  //bSeperatorAfter == TRUE, 0 分隔符后Q_BITS个bit 是r的值
				if(bit == 0)
					zeroCnt++;
				else
					zeroCnt = 0;
				//if(zeroCnt > (Q_BITS + 1))
				//	return;
				r |= (bit << rBitCnt);
				rBitCnt++;
				if(rBitCnt >= Q_BITS){ //r数值获得结束，也就是整个Num获得完成
					uInt32 num = q * M + r;
					//printf("q = %d, r = %d, num=%d\n", q, r, num);
					out.push_back(num);
					bSeperatorAfter = FALSE;
					rBitCnt = 0;
					q = 0;
					r = 0;

					if(out.size() >= needOutNum)
						return;
				}
			}

			in[i] >>= 1;
		}
	}
	return;
}

/**************************************************
Huffman 编码:
	假如有权重为: 5, 29, 7, 8, 14, 23, 3, 11
	那么可以构造huffman 树如下:
	 5    3
 	  \   /
 	    8     7     8     11
 	     \    /      \     /
   14      15          19        23
      \      /             \        /
         29     29           42
           \      /            /
              58             /
                 \           /
                      100
***************************************************/
/* HufffMan 树 */
typedef struct
{
	uInt32 weight;
	uInt32 parent;
	uInt32 leftChild;
	uInt32 rightChild;
}stHuffmanTreeNode;

typedef struct
{
	uInt32 leftChild;
	uInt32 rightChild;
}stHuffmanTreeNodeSimple;

/* 由于huffman数组的节点个数不会超过255个，可以通过映射
    到0 ~255的范围*/
/********************************
完整的huffman树如下，叶子节点个数为8个(0 ~ 7号单元)
[w, p, l, r]=0:[5, 8, 0, 0]
[w, p, l, r]=1:[29, 13, 0, 0]
[w, p, l, r]=2:[7, 9, 0, 0]
[w, p, l, r]=3:[8, 10, 0, 0]
[w, p, l, r]=4:[14, 11, 0, 0]
[w, p, l, r]=5:[23, 12, 0, 0]
[w, p, l, r]=6:[3, 8, 0, 0]
[w, p, l, r]=7:[11, 10, 0, 0]
[w, p, l, r]=8:[8, 9, 6, 0]
[w, p, l, r]=9:[15, 11, 2, 8]
[w, p, l, r]=10:[19, 12, 3, 7]
[w, p, l, r]=11:[29, 13, 4, 9]
[w, p, l, r]=12:[42, 14, 10, 5]
[w, p, l, r]=13:[58, 14, 11, 1]
[w, p, l, r]=14:[100, 0, 12, 13]

		||
		\ /

[w, p, l, r]=0:[8, 9, 6, 0]
[w, p, l, r]=1:[15, 11, 2, 8]
[w, p, l, r]=2:[19, 12, 3, 7]
[w, p, l, r]=3:[29, 13, 4, 9]
[w, p, l, r]=4:[42, 14, 10, 5]
[w, p, l, r]=5:[58, 14, 11, 1]
[w, p, l, r]=6:[100, 0, 12, 13]
	      ||
	       \/ 简化
[l, r]=0:[6, 0]
[l, r]=1:[2, 8]
[l, r]=2:[3, 7]
[l, r]=3:[4, 9]
[l, r]=4:[10, 5]
[l, r]=5:[11, 1]
[l, r]=6:[12, 13]
	    ||
	    \/
[l, r]=0:[6, 0]
[l, r]=1:[2, 1]  (2, 8-7)
[l, r]=2:[3, 7]
[l, r]=3:[4, 2]  (4, 9-7)
[l, r]=4:[3, 5]  (10-7, 5)
[l, r]=5:[4, 1]  (11-7, 1)
[l, r]=6:[5, 6]  (12-7,13-7)	同时标记下该值是映射后的值  

可以用bit: 0 表示没有经过映射，是叶子节点的index
用
*********************************/
#pragma pack (1)
typedef struct
{
	//uInt8 childIsMap; //低4 bit用来标识leftChild和高4 bit用来标识rightChild是否经过map
	uInt8 leftChild;    
	uInt8 rightChild;
}stHuffmanTreeNodeCharSimple; /* 专门为char进行编码 */
#pragma pack ()

typedef struct
{
	uInt32 weight;
	uInt32 index;
}stWeightToIdx;

void Merge(stWeightToIdx *arr, uInt32 low, uInt32 mid, uInt32 high)
{
	//将两个有序区归并为一个有序区
	uInt32 i = low, j = mid + 1, k = 0;
	stWeightToIdx *temp = new stWeightToIdx[high-low+1];
	while(i <= mid && j <= high)
	{
		if(arr[i].weight <= arr[j].weight){
			temp[k++] = arr[i++];
		}else{
			temp[k++] = arr[j++];
		}
	}
	while(i <= mid) {temp[k++] = arr[i++];}
	while(j <= high) {temp[k++] = arr[j++];}
	for(i = low, k=0; i <= high; i++, k++){
		arr[i] = temp[k];
	}
	delete []temp;
}

/* 二路归并排序: Average: O(nlog2n), Best: O(nlog2n), Worst: O(nlog2n) */
void my_merge_sort_weight(stWeightToIdx *arr, uInt32 n)//参数和递归略不同， n 代表数组中元素个数，即数组最大下标是 n-1
{
	int size = 1, low, mid, high;
	while(size <= n-1)
	{
		low = 0;
		while(low+size <= n-1)
		{
			mid = low + size-1;
			high = mid + size;
			if(high > n - 1){//第二个序列个数不足 size
				high = n - 1;
			}
			Merge(arr,low, mid, high);//调用归并子函数
			low = high + 1;//下一次归并时第一关序列的下界
		}
		size *= 2;//范围扩大一倍
	}
}


/*n个叶子节点有2n-1个节点*/
/*
	获得的huffman 树(用数组存储的)前n个元素存放的是叶子节点。
	后n -1个元素存放的是叶子节点的父节点
	pRealLeafNum为pWeight数组的n个元素实际权重值不为0的个数，
	权重为0不参与建立huffman树过程
	例如: 权重分别为:   0, 5, 29, 7, 0 , 8, 14, 23, 3, 11, 0 有三个0 
	建立的huffman树如下:

		[w, p, l, r]=0:[0, 0, 0, 0]
		[w, p, l, r]=1:[5, 14, 0, 0]
		[w, p, l, r]=2:[29, 19, 0, 0]
		[w, p, l, r]=3:[7, 15, 0, 0]
		[w, p, l, r]=4:[0, 0, 0, 0]
		[w, p, l, r]=5:[8, 16, 0, 0]
		[w, p, l, r]=6:[14, 17, 0, 0]
		[w, p, l, r]=7:[23, 18, 0, 0]
		[w, p, l, r]=8:[3, 14, 0, 0]
		[w, p, l, r]=9:[11, 16, 0, 0]
		[w, p, l, r]=10:[0, 0, 0, 0]
		
		[w, p, l, r]=11:[0, 0, 0, 0]   //空出来三个空间
		[w, p, l, r]=12:[0, 0, 0, 0]
		[w, p, l, r]=13:[0, 0, 0, 0]
		
		[w, p, l, r]=14:[8, 15, 8, 1]
		[w, p, l, r]=15:[15, 17, 3, 14]
		[w, p, l, r]=16:[19, 18, 5, 9]
		[w, p, l, r]=17:[29, 19, 6, 15]
		[w, p, l, r]=18:[42, 20, 16, 7]
		[w, p, l, r]=19:[58, 20, 17, 2]
		[w, p, l, r]=20:[100, 0, 18, 19]
	
*/
stHuffmanTreeNode* create_huffman_tree(uInt32 *pWeight, uInt32 n, uInt32 *pRealLeafNum)
{
	if(n <= 1 || !pWeight)
		return NULL;

	uInt32 m = 2 * n - 1;
	stHuffmanTreeNode *pHuffmanTree = NULL; 
	pHuffmanTree = new stHuffmanTreeNode[m];
	memset(pHuffmanTree, 0, sizeof(stHuffmanTreeNode) * m);

	stWeightToIdx *pWeightToIdx = new stWeightToIdx[n](); /* 用于排序实现快速查找最小的两个节点 */
	uInt32 i = 0, realLeafNum = 0;
	/* 0到n-1 存放叶子节点 */
	for(; i < n; i++){
		if(pWeight[i] > 0){
			pHuffmanTree[i].weight = pWeight[i];
			/* 记录权重和所在数组下标的映射 */
			pWeightToIdx[realLeafNum].weight = pWeight[i];
			pWeightToIdx[realLeafNum].index = i;
			realLeafNum++;
		}
	}
	my_printf("n = %d, realLeafNum = %d\n", n , realLeafNum);
	*pRealLeafNum = realLeafNum;

	/* 从小到大按权重进行排序 */
	//my_qsort_weight(pWeightToIdx, 0, n-1);
	my_merge_sort_weight(pWeightToIdx, realLeafNum);
	//for(i = 0; i < realLeafNum; i++){
	//	printf("(weight, index)=(%d,%d)\n", pWeightToIdx[i].weight, pWeightToIdx[i].index);
	//}

	uInt32 start = 0;
	/*n到m存放其他节点  */
	i = n + (n - realLeafNum); //少realLeafNum-n 个叶子节点就往后移动几个单元
	for(; i < m; i++){
		/*从start 到n-1中选出最小的两个根节点进行合并*/
		uInt32 left = pWeightToIdx[start].index;
		uInt32 right = pWeightToIdx[start+1].index;
		pHuffmanTree[i].weight = pHuffmanTree[left].weight + pHuffmanTree[right].weight;
		pHuffmanTree[i].leftChild = left;
		pHuffmanTree[i].rightChild = right;
		
		pHuffmanTree[left].parent = i;
		pHuffmanTree[right].parent = i;

		/* 将start 和start+1合并后放在start的位置 */
		pWeightToIdx[start].index = i;
		pWeightToIdx[start].weight = pHuffmanTree[i].weight;

		/* 由于是排好序的只需要交换少量的数据 */
		uInt32 j = start+2;
		for(; j < realLeafNum; j++){
			if(pWeightToIdx[start].weight < pWeightToIdx[j].weight){
				pWeightToIdx[j - 1].weight = pWeightToIdx[start].weight;
				pWeightToIdx[j - 1].index = pWeightToIdx[start].index;
				break;
			}

			/* 如果pWeightToIdx[start].weight 大于j的weight, 则将j前移一位  */
			pWeightToIdx[j - 1].weight = pWeightToIdx[j].weight;
			pWeightToIdx[j - 1].index = pWeightToIdx[j].index;
		}

		/* 如果pWeightToIdx[start].weight 是最大的则放在realLeafNum-1的位置 */
		if(j >= realLeafNum){
			pWeightToIdx[realLeafNum - 1].weight = pWeightToIdx[start].weight;
			pWeightToIdx[realLeafNum - 1].index = pWeightToIdx[start].index;
		}

		//for(j = start+1; j < n; j++){
		//	my_printf("(weight, index)=(%d,%d)\n", pWeightToIdx[j].weight, pWeightToIdx[j].index);
		//}
		//cout << "--------------" <<endl;

		start++;
	}

	delete [] pWeightToIdx;
	pWeightToIdx = NULL;

	return pHuffmanTree;
}

/* n 个叶子节点，这是已知叶子节点在0到n-1号单元 */
void huffman_encode(stHuffmanTreeNode *pHuffmanTree, uInt32 n, vector<uInt32> &outCode)
{
	if(!pHuffmanTree)
		return;
	if(n <= 1)
		return;

	uInt8 *pCode = new uInt8[n]();
	uInt32 nodeMaxNum = 2 * n - 1;

	uInt8 bitCnt = 0;
	bitset<BIT_NUMS> oneItem;
	oneItem.reset();
	uInt32 i = 0;
	/* 遍历前n 个叶子节点 */
	for(; i < n; i++){
		if(pHuffmanTree[i].weight == 0) //如果叶子节点的权重为0 不参与编码
			continue;
		/* 从叶子节点开始逆向获得编码 */
		uInt32 start = n - 1;
		/* check一下是真的叶子节点 */
		if((pHuffmanTree[i].leftChild == 0) && (pHuffmanTree[i].rightChild == 0)){
			uInt32 parentIdx = pHuffmanTree[i].parent;
			uInt32 curIdx = i;
			while((parentIdx < nodeMaxNum) && (parentIdx != 0)){
				/* 如果当前节点是父节点的左孩子 */
				if(pHuffmanTree[parentIdx].leftChild == curIdx){
					pCode[start--] = '0';
					//cout << " " << 0;
				}
				else{
					pCode[start--] = '1';
					//cout << " " << 1;
				}

				curIdx = parentIdx;
				parentIdx = pHuffmanTree[parentIdx].parent;
			}
		}

		printf("(%d,%d)%d huffman code is: ",start, n, pHuffmanTree[i].weight);
		uInt32 j = start + 1;
		for(; j < n; j++){
			//printf("%c ", pCode[j]);
			if(bitCnt >= BIT_NUMS){
				cout << endl;
				bitCnt = 0;
				cout << "encodeBits = " << oneItem << endl;
				outCode.push_back(oneItem.to_ulong());
				oneItem.reset();
			}

			if(pCode[j] == '1'){
				oneItem.set(bitCnt++);
				cout << " " << 1;
			}
			else{
				oneItem.reset(bitCnt++);
				cout << " " << 0;
			}
		}

		cout << endl;
	}

	if(bitCnt != 0){
		bitCnt = 0;
		cout << "encodeBits = " << oneItem << endl;
		outCode.push_back(oneItem.to_ulong());
		oneItem.reset();
	}
	
	delete [] pCode;
	return;
}

void huffman_decode(
	stHuffmanTreeNode *pHuffmanTree,
	vector<uInt32> &huffmanCode,
	uInt32 *pWeight,
	uInt32 n)
{
	if(!pHuffmanTree || !pWeight)
		return;
	if(n <= 1)
		return;
	uInt32 i = 0, j = 0;
	uInt32 m = 2 * n - 1;
	uInt32 start = m - 1;
	for(; i < huffmanCode.size(); i++){
		uInt32 code = huffmanCode[i];
		uInt8 bitCnt = 0;
		while(bitCnt < BIT_NUMS){
			uInt8 bit = code & 0x01;
			if(pHuffmanTree[start].leftChild == 0 && pHuffmanTree[start].rightChild == 0){
				//cout << " j = " << j << endl;
				pWeight[j++] = pHuffmanTree[start].weight;
				start = m - 1;
				if(j >= n){ /* n 个叶子节点都解码完 */
					return;
				}
			}
			else{
				if(bit == 0){
					//cout << " " << 0;
					start = pHuffmanTree[start].leftChild;
				}else{
					//cout << " " << 1;
					start = pHuffmanTree[start].rightChild;
				}

				code >>= 1;
				bitCnt++;
			}
		}
	}
	return;
}

/* 因为是用数组存储的huffman 树，数组的最后一个元素就是父
	节点，所以只需知道左右子树的数组index保存即可，
	可以把数组0 到n - 1的元素去掉，因为0到n-1保存的就是
	叶子节点。该解码函数返回的是叶子节点的index值从0
	到n - 1. 解码输出为叶子节点在huffman数组中的index索引
	
[w, p, l, r]=0:[5, 8, 0, 0]
[w, p, l, r]=1:[29, 13, 0, 0]
[w, p, l, r]=2:[7, 9, 0, 0]
[w, p, l, r]=3:[8, 10, 0, 0]
[w, p, l, r]=4:[14, 11, 0, 0]
[w, p, l, r]=5:[23, 12, 0, 0]
[w, p, l, r]=6:[3, 8, 0, 0]
[w, p, l, r]=7:[11, 10, 0, 0]
[w, p, l, r]=8:[8, 9, 6, 0]
[w, p, l, r]=9:[15, 11, 2, 8]
[w, p, l, r]=10:[19, 12, 3, 7]
[w, p, l, r]=11:[29, 13, 4, 9]
[w, p, l, r]=12:[42, 14, 10, 5]
[w, p, l, r]=13:[58, 14, 11, 1]
[w, p, l, r]=14:[100, 0, 12, 13]

		||
		\ /

[w, p, l, r]=0:[8, 9, 6, 0]
[w, p, l, r]=1:[15, 11, 2, 8]
[w, p, l, r]=2:[19, 12, 3, 7]
[w, p, l, r]=3:[29, 13, 4, 9]
[w, p, l, r]=4:[42, 14, 10, 5]
[w, p, l, r]=5:[58, 14, 11, 1]
[w, p, l, r]=6:[100, 0, 12, 13]
	      ||
	       \/ 简化
[l, r]=0:[6, 0]
[l, r]=1:[2, 8]
[l, r]=2:[3, 7]
[l, r]=3:[4, 9]
[l, r]=4:[10, 5]
[l, r]=5:[11, 1]
[l, r]=6:[12, 13]
		||
	      \ / 第一步:求和压缩
	得到序列:  6; 6+0 => 6+14=20 ; 20+2; 24+8; 32+3; 35+7; 42+4......
	注意:其中6+0的处理为了避免出现两个6的情况，所以加
	上14这个超过范围的值也就是(2*n-1)
	得到序列:  6 20 24 32 35 42 46 55 65 70 81 82 94 107 (2*6+2个数是递增的)
		||
		\/
	把6单独拿出来，
	解码只需逆推递减: 6 (20-6=14 > 13) => 0 24-20 = 4......
	注意: 由于20-4 得到的值大于有效最大值13则为0
	    ||
	    \ / 第二步: 用bitmap进行压缩(可能会浪费太多空间)
	0 0 0 0 0 1 0 ............0 1 0 .....
				13个0
	缺点: 会浪费加的2*n-1个0空间
*/
void huffman_decode_simple(
	stHuffmanTreeNodeSimple *pHuffmanTree,
	vector<uInt32> &huffmanCode,
	uInt32 *pTreeIndex,
	uInt32 n,
	uInt32 realLeafNum)
{
	if(!pHuffmanTree || !pTreeIndex)
		return;
	if(n <= 1)
		return;
	uInt32 i = 0, j = 0;
	uInt32 m = realLeafNum - 1; // n 个叶子节点，有n - 1个节点
	uInt32 start = m - 1;
	printf("huffmanCode.size() = %d\n", huffmanCode.size());
	for(; i < huffmanCode.size(); i++){
		uInt32 code = huffmanCode[i];
		printf("code = %x\n", huffmanCode[i]);
		uInt8 bitCnt = 0;
		while(bitCnt < BIT_NUMS){
			uInt8 bit = code & 0x01;
			if(bit == 0){
				//cout << " " << 0;
				start = pHuffmanTree[start].leftChild;
			}else{
				//cout << " " << 1;
				start = pHuffmanTree[start].rightChild;
			}

			code >>= 1;
			bitCnt++;
			
			if(start < n){ // start 的值为0 ~ n-1则为叶子节点
				//cout << " j = " << j << endl;
				pTreeIndex[j++] = start;
				start = m - 1;
				if(j >= realLeafNum){ /* realLeafNum 个叶子节点都解码完 */
					return;
				}
			}
			else{
				start -= n;
				start -= (n - realLeafNum);
			}
		}
	}
	return;
}

/*****************************************************
	专门为char 的huffman编解码函数
*****************************************************/
void huffman_encode_char(
	uInt8 *pChar, //char 的值就是叶子节点的index
	uInt32 charBytes,
	stHuffmanTreeNode *pHuffmanTree, // 已经创建好的huffman树
	uInt32 leafNum,                        // huffman树叶子节点个数
	vector<uInt32> &outCode)         //输出的huffman编码
{
	if(!pHuffmanTree)
		return;
	if(leafNum <= 1)
		return;

	uInt8 *pCode = new uInt8[leafNum]();
	uInt32 nodeMaxNum = 2 * leafNum - 1;

	uInt8 bitCnt = 0;
	bitset<BIT_NUMS> oneItem;
	oneItem.reset();
	uInt32 i = 0;
	/* 遍历cmpOutList  */
	for(; i < charBytes; i++){
		/* 从叶子节点开始逆向获得编码 */
		uInt32 start = leafNum - 1;
		uInt32 leafIndx = (uInt8)(pChar[i] & 0xff);
		
		/* check一下是真的叶子节点 */
		if((pHuffmanTree[leafIndx].leftChild == 0) && (pHuffmanTree[leafIndx].rightChild == 0)){
			uInt32 parentIdx = pHuffmanTree[leafIndx].parent;
			uInt32 curIdx = leafIndx;
			while((parentIdx < nodeMaxNum) && (parentIdx != 0)){
				/* 如果当前节点是父节点的左孩子 */
				if(pHuffmanTree[parentIdx].leftChild == curIdx){
					pCode[start--] = '0';
					//cout << " " << 0;
				}
				else{
					pCode[start--] = '1';
					//cout << " " << 1;
				}

				curIdx = parentIdx;
				parentIdx = pHuffmanTree[parentIdx].parent;
			}
		}

		my_printf("%d huffman code is: ",pChar[i]);
		uInt32 j = start + 1;
		for(; j < leafNum; j++){
			//my_printf("%c ", pCode[j]);
			if(bitCnt >= BIT_NUMS){
				//cout << endl;
				bitCnt = 0;
				//cout << "encodeBits = " << oneItem << endl;
				outCode.push_back(oneItem.to_ulong());
				oneItem.reset();
			}

			if(pCode[j] == '1'){
				oneItem.set(bitCnt++);
				//cout << " " << 1;
			}
			else{
				oneItem.reset(bitCnt++);
				//cout << " " << 0;
			}
		}

		//cout << endl;
	}

	if(bitCnt != 0){
		bitCnt = 0;
		//cout << "encodeBits = " << oneItem << endl;
		outCode.push_back(oneItem.to_ulong());
		oneItem.reset();
	}
	
	delete [] pCode;
	return;
}

void huffman_decode_char(
	stHuffmanTreeNodeSimple *pHuffmanTree,
	vector<uInt32> &huffmanCode,
	uInt8 *pChar,
	uInt32 totalCnt,
	uInt32 leafNum,
	uInt32 realLeafNum)
{
	if(!pHuffmanTree || !pChar)
		return;
	if(leafNum <= 1)
		return;
	uInt32 i = 0, j = 0;
	uInt32 m = realLeafNum - 1; // n 个叶子节点，有n - 1个节点
	uInt32 start = m - 1;

	for(i = 0; i < realLeafNum - 1; i++){
		my_printf("pSimpleHuffmanTree[%d](l, r)= (%d, %d)\n", i,
			pHuffmanTree[i].leftChild, pHuffmanTree[i].rightChild);
	}
	
	//printf("huffmanCode.size() = %d\n", huffmanCode.size());
	for(i = 0; i < huffmanCode.size(); i++){
		uInt32 code = huffmanCode[i];
		my_printf("code = %x\n", huffmanCode[i]);
		uInt8 bitCnt = 0;
		while(bitCnt < BIT_NUMS){
			uInt8 bit = code & 0x01;
			if(bit == 0){
				//cout << " " << 0;
				start = pHuffmanTree[start].leftChild;
			}else{
				//cout << " " << 1;
				start = pHuffmanTree[start].rightChild;
			}

			code >>= 1;
			bitCnt++;

			//cout << " start = " << start << endl;
			if(start < leafNum){ // start 的值为0 ~ n-1则为叶子节点
				pChar[j++] = (uInt8)(start & 0xff);
				start = m - 1;
				if(j >= totalCnt){
					return;
				}
			}
			else{
				start -= leafNum;
				start -= (leafNum - realLeafNum);
			}
		}
	}
	return;
}

/* 返回值为pWritePointer 地址指针需要移动的字节数 */
uInt32 my_huffman_encode_char(uInt8 *pSrcChar, uInt32 charNum, uInt8 *pWritePointer)
{
	if(!pSrcChar || !pWritePointer || charNum == 0)
		return 0;
	my_warning("---------------my_huffman_encode_char---------------- \n");
	uInt32 totalEncodeBytes = 0;
	uInt8 *pOutData = pWritePointer;
	/* (1) 统计字符c的权重 */
	my_warning("###Start count char weight:\n");
	uInt32 j = 0;
	uInt32 pCharWeight[256] = {0}; /* 保存c 值重复的个数 */
	for(j = 0; j < charNum; j++){
		pCharWeight[pSrcChar[j] & 0xff]++;
	}

	my_warning("charNum = %d\n", charNum);

	/* (2) 为c 元素建立huffman树 */
	my_warning("###start create pCharHuffmanTree:\n");
	stHuffmanTreeNode *pCharHuffmanTree = NULL;
	uInt32 realLeafNum = 0;
	pCharHuffmanTree = create_huffman_tree(pCharWeight, 256, &realLeafNum);
	my_warning("pCharHuffmanTree realLeafNum = %d\n", realLeafNum); 

	/* (3) pCharHuffmanTree树简化, 建立映射表并保存 */
	my_warning("###start simpfy pCharHuffmanTree and save:\n");
	uInt8 charSimpleHuffmanTreeSize = 0;
	if(realLeafNum > 1){
		charSimpleHuffmanTreeSize = (realLeafNum - 1) & 0xff;
	}
	else{
		charSimpleHuffmanTreeSize = 0;
	}
	
	stHuffmanTreeNodeCharSimple *pCharHuffmanTreeSimple = new stHuffmanTreeNodeCharSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimple, NULL);

	uInt8 bitMapNum = (charSimpleHuffmanTreeSize*2) / 8; //左右节点的index都需要映射
	//bitMapNum = ((charSimpleHuffmanTreeSize*2) % 8 == 0) ? bitMapNum : (bitMapNum+1);
	bitMapNum = (GET_MOD(charSimpleHuffmanTreeSize*2, 8) == 0) ? bitMapNum : (bitMapNum+1);
	uInt8 pCharHuffmanTreeBitMap[64] = {0}; 

	my_warning("charSimpleHuffmanTreeSize = %d, bitMapNum = %d\n", charSimpleHuffmanTreeSize, bitMapNum);

	uInt16 bitPos = 0;
	for(j = 0; j < charSimpleHuffmanTreeSize; j++){
		uInt32 leftChildIdx = pCharHuffmanTree[j + 256+(256-realLeafNum)].leftChild;
		uInt32 rightChildIdx = pCharHuffmanTree[j + 256+(256-realLeafNum)].rightChild;
		if(leftChildIdx >= 256){
			setBit_uInt8(pCharHuffmanTreeBitMap, bitPos++); //如果大于叶子节点的个数则需要映射
			pCharHuffmanTreeSimple[j].leftChild = (leftChildIdx - 256) & 0xff;
		}
		else{
			pCharHuffmanTreeSimple[j].leftChild = leftChildIdx & 0xff;
			bitPos++;
		}

		if(rightChildIdx >= 256){
			setBit_uInt8(pCharHuffmanTreeBitMap, bitPos++); //如果大于叶子节点的个数则需要映射
			pCharHuffmanTreeSimple[j].rightChild = (rightChildIdx - 256)  & 0xff;
		}
		else{
			pCharHuffmanTreeSimple[j].rightChild = rightChildIdx & 0xff;
			bitPos++;
		}
	}

	//fwrite(&charSimpleHuffmanTreeSize, sizeof(uInt8), 1, pFout); //这个值不会超过256所以一个字节就可以了
	memcpy(pOutData, &charSimpleHuffmanTreeSize, sizeof(uInt8));
	pOutData += sizeof(uInt8);
	totalEncodeBytes += sizeof(uInt8);
	//fwrite(pCharHuffmanTreeBitMap, sizeof(uInt8) * bitMapNum, 1, pFout); //写入映射表
	memcpy(pOutData, pCharHuffmanTreeBitMap, sizeof(uInt8) * bitMapNum);
	pOutData += sizeof(uInt8) * bitMapNum;
	totalEncodeBytes += sizeof(uInt8) * bitMapNum;

	//fwrite(pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple), 1, pFout);
	memcpy(pOutData, pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	pOutData += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);
	totalEncodeBytes += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);
	
	delete [] pCharHuffmanTreeSimple;
	pCharHuffmanTreeSimple = NULL;

	/* (4) 对char 进行huffman 编码 */
	my_warning("### start huffman encode for char:\n");
	vector<uInt32> charHuffmanCode;
	huffman_encode_char(pSrcChar, charNum, pCharHuffmanTree, 256, charHuffmanCode);
	
	uInt32 *pCharHuffmanCode = new uInt32[charHuffmanCode.size()]();
	ASSERT_RELEASE((void*)pCharHuffmanCode, NULL);
	for(j = 0; j < charHuffmanCode.size(); j++){
		pCharHuffmanCode[j] = charHuffmanCode[j];
	}
	memcpy(pOutData, &j, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	totalEncodeBytes += sizeof(uInt32);
	memcpy(pOutData, pCharHuffmanCode, sizeof(uInt32) * j);
	pOutData += sizeof(uInt32) * j;
	totalEncodeBytes += j * sizeof(uInt32);

	delete [] pCharHuffmanCode;
	pCharHuffmanCode = NULL;
	delete [] pCharHuffmanTree;
	pCharHuffmanTree = NULL;
	my_warning("@@@@@@ char huffman encode total bytes = %d\n", totalEncodeBytes);
	
	my_warning("************************data struct*************************\n");
	my_warning("charSimpleHuffmanTreeSize: 1 bytes\n");
	my_warning("pCharHuffmanTreeBitMap: %d bytes\n",sizeof(uInt8) * bitMapNum);
	my_warning("pCharHuffmanTreeSimple: %d bytes\n", charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	my_warning("pCharHuffmanCodeSize: 4 bytes\n");
	my_warning("pCharHuffmanCode: %d bytes\n",j * sizeof(uInt32));
	my_warning("**********************************************************\n");

	my_warning("---------------my_huffman_encode_char END---------------- \n");
	return totalEncodeBytes;
}

/* 返回值为pSrcData 地址指针需要移动的字节数 */
uInt32 my_huffman_decode_char(uInt8 *pSrcData, uInt8 *pCharOut, uInt32 charNum)
{
	if(!pSrcData || !pCharOut)
		return 0;
	my_warning("---------------my_huffman_decode_char---------------- \n");
	uInt32 totalDecodeBytes = 0;
	uInt8 *pInData = pSrcData;
	/* 解压char 部分 */
	uInt8 charSimpleHuffmanTreeSize = (uInt8)*pInData;
	pInData += sizeof(uInt8);
	totalDecodeBytes += sizeof(uInt8);

	/* 获得char 的简单huffman树 */
	stHuffmanTreeNodeSimple *pCharHuffmanTreeSimple = new stHuffmanTreeNodeSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimple, NULL);
	stHuffmanTreeNodeCharSimple *pCharHuffmanTreeSimpleTmp = new stHuffmanTreeNodeCharSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimpleTmp, pCharHuffmanTreeSimple, NULL);

	uInt8 bitMapNum = (charSimpleHuffmanTreeSize*2) / 8; //左右节点的index都需要映射
	//bitMapNum = ((charSimpleHuffmanTreeSize*2) % 8 == 0) ? bitMapNum : (bitMapNum+1);
	bitMapNum = (GET_MOD(charSimpleHuffmanTreeSize*2, 8) == 0) ? bitMapNum : (bitMapNum+1);
	uInt8 pCharHuffmanTreeBitMap[64] = {0}; //最大64 = 256 * 2 /8

	my_warning("charSimpleHuffmanTreeSize = %d, bitMapNum = %d\n", charSimpleHuffmanTreeSize, bitMapNum);

	memcpy(pCharHuffmanTreeBitMap, pInData, sizeof(uInt8) * bitMapNum); //获取映射表数据
	pInData += sizeof(uInt8) * bitMapNum;
	totalDecodeBytes += sizeof(uInt8) * bitMapNum;
	memcpy(pCharHuffmanTreeSimpleTmp, pInData, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	pInData += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);
	totalDecodeBytes += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);

	uInt32 i = 0, bitPos = 0;
	for(i = 0; i < charSimpleHuffmanTreeSize; i++){
		enBool isMap = FALSE;
		isMap = tstBit_uInt8(pCharHuffmanTreeBitMap, bitPos++);
		if(isMap){
			pCharHuffmanTreeSimple[i].leftChild = pCharHuffmanTreeSimpleTmp[i].leftChild + 256;
		}
		else{
			pCharHuffmanTreeSimple[i].leftChild = pCharHuffmanTreeSimpleTmp[i].leftChild;
		}
		isMap = tstBit_uInt8(pCharHuffmanTreeBitMap, bitPos++);
		if(isMap){
			pCharHuffmanTreeSimple[i].rightChild = pCharHuffmanTreeSimpleTmp[i].rightChild + 256;
		}
		else{
			pCharHuffmanTreeSimple[i].rightChild = pCharHuffmanTreeSimpleTmp[i].rightChild;
		}
	}

	delete [] pCharHuffmanTreeSimpleTmp;
	pCharHuffmanTreeSimpleTmp = NULL;

	/* 获得char 的huffman编码uInt32 的个数 */
	uInt32 charHuffmanCodeNums = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	totalDecodeBytes += sizeof(uInt32);
	my_warning("charHuffmanCodeBytes = %d\n", charHuffmanCodeNums * sizeof(uInt32));

	vector<uInt32> charHuffmanCode;
	for(i = 0; i < charHuffmanCodeNums; i++){
		uInt32 codeValue = *((uInt32*)pInData);
		charHuffmanCode.push_back(codeValue);
		pInData += sizeof(uInt32);
	}

	totalDecodeBytes += sizeof(uInt32) * charHuffmanCodeNums;

	huffman_decode_char(pCharHuffmanTreeSimple, 
						charHuffmanCode,
						pCharOut,
						charNum,
						256,
						charSimpleHuffmanTreeSize+1); //实际的叶子节点数比简单huffman数组个数多一个

	delete [] pCharHuffmanTreeSimple;
	pCharHuffmanTreeSimple = NULL;
	my_warning("---------------my_huffman_decode_char END---------------- \n");
	return totalDecodeBytes;
}

static uInt32 read_file_content(void *pOut, uInt32 cnt, FILE* fd)
{
	if(pOut == NULL)
		return 0;
	uInt32 cntBytes = 0;
	uInt8 *pData = (uInt8*)pOut;
	cntBytes = fread(pData, 1, cnt, fd);
	return cntBytes;
}

static void my_dump_data(const char* fileName, void *pData, uInt32 bytes)
{
#if NEED_DUMP_DATA
	if(!fileName || !pData)
		return;
	FILE *pFd = NULL;
	pFd = fopen(fileName, "wb");
	fwrite(pData, bytes, 1, pFd);
	fclose(pFd);
#endif
	return;
}

typedef struct{
	int sec;  //代表目前秒数, 正常范围为0-59, 但允许至61 秒
	int min;  //代表目前分数, 范围0-59
	int hour;  //从午夜算起的时数, 范围为0-23
	int mday;  //目前月份的日数, 范围01-31
	int mon;  //代表目前月份, 从一月算起, 范围从0-11
	int year;  //从1900 年算起至今的年数
	int wday;  //一星期的日数, 从星期一算起, 范围为0-6
	int yday;  //从今年1 月1 日算起至今的天数, 范围为0-365
	int isdst;  //日光节约时间的旗标
}stDate;

Int32 my_get_current_date(stDate *pDateOut)
{
    time_t timep = 0;
    struct tm *utc_tm ;
    // get time
    timep = time(NULL);
    //utc_tm = gmtime(&timep);
	struct tm *local_tm = localtime(&timep);
    memset(pDateOut, 0, sizeof(struct tm));
    if (local_tm != NULL){
        memcpy(pDateOut, local_tm, sizeof(struct tm));
		pDateOut->year += 1900;
		pDateOut->mon += 1;
        return 0;
    }
    return -1;
}

/* return ms */
Int32 my_calc_process_time(Int32 *pStartMs)
{
	struct timespec endTime;
	clock_gettime(CLOCK_REALTIME, &endTime);
	if(pStartMs){
		return endTime.tv_sec * 1000 + endTime.tv_nsec / 1000000 - *pStartMs;
	}
	return endTime.tv_sec * 1000 + endTime.tv_nsec / 1000000;
}
/************** LZ77 编解码算法**********************/
/*
举例:  a a c a a c a b c a b a a a c
	 如果当前cursor 位于b和c间:  a a c a b | c a b a
	 匹配子串为c a b, 则stCmpCp.p = 3, stCmpCp.l = 3, stCmpCp.c = a
*/

//LZ77压缩算法原理:http://www.cnblogs.com/en-heng/p/4992916.html
//http://www.cnblogs.com/napoleon_liu/archive/2010/12/16/1908573.html
#define USE_GOLOMB_ENCODE (1)

#if USE_GOLOMB_ENCODE /* 如果使用golomb 编码来存储 stLZ77CmpCp*/
#define SLIDE_WIN_LEN (2048 - 1) /* 滑动窗口大小 */
#define CUR_BUFF_LEN  (258) /* 待编码窗口大小 */
#define P_BITS        (11)
#define MIN_MATCH_LEN (3)
#define MAX_MATCH_LEN (258)

#pragma pack (1)
typedef struct
{
	uInt32 p; 
	uInt32 l; 
	uInt8 c; /* 匹配子串后一个字符 */
}stLZ77CmpCp; /* 压缩后输出的数据对 */
#pragma pack ()

#else
#define SLIDE_WIN_LEN (31) /* 滑动窗口大小 */
#define CUR_BUFF_LEN  (7) /* 待编码窗口大小 */

typedef struct
{
	uInt8 p : 5; /* 匹配子串的第一字符离cursor 位置的距离*/
	uInt8 l : 3; /* 匹配的长度CUR_BUFF_LEN = 7 用3 个bit 来存储就够了 */
	uInt8 c; /* 匹配子串后一个字符 */
}stLZ77CmpCp; /* 压缩后输出的数据对 */
#endif

/* 将pBitSrc 数组的每个数字的低lowBitsNum 位组合成新的数字 */
void combine_bits(uInt32 *pBitSrc, uInt32 num, uInt8 lowBitsNum, uInt8 *pCmbOut)
{
	if(!pBitSrc || num == 0 || !pCmbOut){
		return;
	}

	memset(pCmbOut, 0, ((lowBitsNum * num) / 8 + 1) * sizeof(uInt8));
	
	uInt32 i = 0;
	uInt32 bitPos = 0;
	for(; i < num; i++){
		uInt8 bitCnt = 0;
		for(; bitCnt < lowBitsNum; bitCnt++){
			uInt8 bit = (pBitSrc[i] >> bitCnt) & 0x01;
			if(bit == 1){
				setBit_uInt8(pCmbOut, bitPos);
			}
			bitPos++;
		}
	}
	return;
}

void decombine_bits(uInt8 *pCmbData, uInt32 num, uInt8 lowBitsNum, uInt32 *pOut)
{
	if(!pOut || num == 0 || !pCmbData){
		return;
	}
	
	uInt32 bitPos = 0, cntNum = 0;
	uInt32 value = 0;
	while(cntNum < num){
		if(tstBit_uInt8(pCmbData, bitPos++)){
			//value |= (0x01 << ((bitPos-1) % lowBitsNum));
			value |= (0x01 << (GET_MOD(bitPos-1, lowBitsNum)));
		}
		
		//if((bitPos % lowBitsNum) == 0){
		if(GET_MOD(bitPos, lowBitsNum) == 0){
			pOut[cntNum] = value;
			value = 0;
			cntNum++;
		}
	}
	
	return;
}

//KMP算法: http://www.61mon.com/index.php/archives/183/
void get_next(uInt8 *pStr, Int32 len, Int32 *pNext)
{
	Int32 i = 0, j = -1;   
	pNext[0] = -1;

	while (i < len){
		if (j == -1 || pStr[i] == pStr[j]){
			i++;
			j++;
			pNext[i] = j;
		}
		else{
			j = pNext[j];
		}
	}
	return;
}

/* 返回子串在主串中第一次出现的位置 */
Int32 KMP_Search(uInt8 *pMainStr, Int32 mainLen, uInt8 *pSubStr, Int32 subLen, Int32 *pNext)
{
	get_next(pSubStr, subLen, pNext);

	Int32 i = 0, j = 0;  
	while (i < mainLen && j < subLen){
		if (j == -1 || pMainStr[i] == pSubStr[j]){
			i++;
			j++;
		}
		else{
			j = pNext[j];
		}
	}

	if (j == subLen){
		return i - j;
	}

	return -1;
}


/* 返回子串在主串中第一次出现的位置 */
Int32 KMP_Search_LZ77(uInt8 *pMainStr, Int32 mainLen, uInt8 *pSubStr, Int32 subLen, Int32 *pNext, Int32 stopIdx)
{
	Int32 i = 0, j = 0;  
	while (i < mainLen && j < subLen){
		if (j == -1 || pMainStr[i] == pSubStr[j]){
			i++;
			j++;
		}
		else{
			j = pNext[j];
			if((i - j) == stopIdx){
				break;
			}
		}
	}

	if (j == subLen){
		return i - j;
	}

	return -1;
}

Int32 Sunday_Search(uInt8 *pMainStr, Int32 mainLen, uInt8 *pSubStr, Int32 subLen)
{
	//print(pMainStr, mainLen);
	//print(pSubStr, subLen);
	Int32 pos[256] = {0};
	Int32 i = 0;
	for(; i < subLen; i++){
		pos[pSubStr[i] & 0xff] = subLen - i;
	}

	Int32 mainStart = 0, matchLen = 0;
	while((mainStart + subLen) <= mainLen){
		//print(&pMainStr[mainStart], mainLen);
		//print(pSubStr, subLen);
		//printf("mainStart=%d,matchLen=%d\n",mainStart,matchLen);
		if(pMainStr[mainStart+matchLen] == pSubStr[matchLen]){
			++matchLen;
			if(matchLen == subLen){
				return mainStart;
			}
		}
		else{
			uInt8 c = pMainStr[mainStart+subLen] & 0xff;
			if(pos[c] != 0){
				matchLen = 0;
				mainStart += pos[c];
				//cout << "+++++++" << pos[c] <<  endl;
			}
			else{
				mainStart += (subLen + 1);
				//cout << "======" << endl;
				matchLen = 0;
			}
		}
	}
	return -1;
}

#if USE_GOLOMB_ENCODE
void longest_match_sunday(uInt8 *pData, uInt32 len, uInt32 cursor_start, stLZ77CmpCp *pCmpCp)
{
	pCmpCp->p = 0;
	pCmpCp->l = 0;
	pCmpCp->c = pData[cursor_start];
	if(cursor_start == 0){
		return;
	}
	
	uInt32 cursor_end = cursor_start + (((cursor_start + CUR_BUFF_LEN) <= len) ? CUR_BUFF_LEN : (len - cursor_start));
	uInt32 slide_start = (cursor_start > SLIDE_WIN_LEN) ? (cursor_start - SLIDE_WIN_LEN) : 0; 
	uInt32 nextMainStrIdx = slide_start;

	Int32 subStrLen = cursor_end - cursor_start - 1;
	if(subStrLen < MIN_MATCH_LEN){
		return;		
	}
	
	Int32 matchLen = MIN_MATCH_LEN;
	for(; matchLen <= subStrLen; matchLen++){
		Int32 mainStrLen = cursor_start - slide_start + matchLen - 1;
		//printf("matchLen = %d, mainStrLen = %d, cursor = %d, nextMainStrIdx = %d\n", 
		//	matchLen, mainStrLen, cursor_start, nextMainStrIdx);
		Int32 match_idx = Sunday_Search(&pData[nextMainStrIdx], mainStrLen, &pData[cursor_start], matchLen);
		//print(&pData[nextMainStrIdx], mainStrLen);
		//print(&pData[cursor_start], matchLen);
		//printf("match_idx = %d\n", match_idx);
		if(match_idx == -1 || (nextMainStrIdx+match_idx) == cursor_start){
			//printf("-------------------\n");
			return;
		}
		else{
			nextMainStrIdx+= match_idx;
			if(nextMainStrIdx >= cursor_start){
				//printf("++++++++++++++++++++++++\n");
				break;
			}
			while(pData[nextMainStrIdx+matchLen] == pData[cursor_start+matchLen]
				&& matchLen < subStrLen){
				matchLen++;
			}
			pCmpCp->p = cursor_start - nextMainStrIdx;
			pCmpCp->l = matchLen;
			pCmpCp->c = pData[cursor_start+matchLen];

			/* 寻找主串开始的位置再一次运用sunday算法 */
			Int32 pos[256] = {0};
			Int32 i = 0;
			for(; i < matchLen+1; i++){
				pos[pData[cursor_start+i] & 0xff] = matchLen + 1 - i;
			}	

			uInt8 c = pData[nextMainStrIdx+matchLen+1] & 0xff;
			if(pos[c] != 0){
				nextMainStrIdx += pos[c];
			}
			else{
				nextMainStrIdx += (matchLen + 1 + 1);
			}

			if(nextMainStrIdx >= cursor_start){
				//printf("++++++++++++++++++++++++\n");
				break;
			}
		}
	}

	return;
}

void longest_match_kmp(uInt8 *pData, uInt32 len, uInt32 cursor_start, stLZ77CmpCp *pCmpCp, Int32 *pNext)
{
	pCmpCp->p = 0;
	pCmpCp->l = 0;
	pCmpCp->c = pData[cursor_start];
	if(cursor_start == 0){
		return;
	}
	
	uInt32 cursor_end = cursor_start + (((cursor_start + CUR_BUFF_LEN) <= len) ? CUR_BUFF_LEN : (len - cursor_start));
	uInt32 slide_start = (cursor_start > SLIDE_WIN_LEN) ? (cursor_start - SLIDE_WIN_LEN) : 0; 
	uInt32 nextMainStrIdx = slide_start;

	Int32 subStrLen = cursor_end - cursor_start - 1;
	if(subStrLen < MIN_MATCH_LEN){
		return;		
	}

       get_next(&pData[cursor_start], subStrLen, pNext);
	
	Int32 matchLen = MIN_MATCH_LEN;
	for(; matchLen <= subStrLen; matchLen++){
		Int32 mainStrLen = cursor_start - slide_start + matchLen - 1;
		//printf("matchLen = %d, mainStrLen = %d, cursor = %d, nextMainStrIdx = %d\n", 
		//	matchLen, mainStrLen, cursor_start, nextMainStrIdx);
		Int32 match_idx = KMP_Search_LZ77(&pData[nextMainStrIdx], mainStrLen, &pData[cursor_start], matchLen, pNext, cursor_start-nextMainStrIdx);
		//print(&pData[nextMainStrIdx], mainStrLen);
		//print(&pData[cursor_start], matchLen);
		//printf("match_idx = %d\n", match_idx);
		if(match_idx == -1 || (nextMainStrIdx+match_idx) == cursor_start){
			return;
		}
		else{
			nextMainStrIdx+= match_idx;
			if(nextMainStrIdx == cursor_start){
				break;
			}
			while(pData[nextMainStrIdx+matchLen] == pData[cursor_start+matchLen]
				&& matchLen < subStrLen){
				matchLen++;
			}
			pCmpCp->p = cursor_start - nextMainStrIdx;
			pCmpCp->l = matchLen;
			pCmpCp->c = pData[cursor_start+matchLen];

			/* 寻找主串开始的位置再一次运用sunday算法 */
			Int32 pos[256] = {0};
			Int32 i = 0;
			for(; i < matchLen+1; i++){
				pos[pData[cursor_start+i] & 0xff] = matchLen + 1 - i;
			}	

			uInt8 c = pData[nextMainStrIdx+matchLen+1] & 0xff;
			if(pos[c] != 0){
				nextMainStrIdx += pos[c];
			}
			else{
				nextMainStrIdx += (matchLen + 1 + 1);
			}
		}
	}
	return;
}

void longest_match_bf(uInt8 *pData, uInt32 len, uInt32 cursor, stLZ77CmpCp *pCmpCp)
{
	pCmpCp->p = 0;
	pCmpCp->l = 0;
	pCmpCp->c = pData[cursor];
	if(cursor == 0){
		return;
	}
	
	uInt32 cursor_start = cursor;
	uInt32 cursor_end = cursor_start + (((cursor + CUR_BUFF_LEN) <= len) ? CUR_BUFF_LEN : (len - cursor));
	uInt32 slide_start = (cursor > SLIDE_WIN_LEN) ? (cursor - SLIDE_WIN_LEN) : 0; 
	uInt32 i = slide_start, j = cursor_start;
	//my_printf("len= %d, cursor_start=%d, cursor_end=%d,slide_start=%d\n",
		//len, cursor_start, cursor_end, slide_start);
	for(; i < cursor; i++){ // slide window substring start index = i
		uInt32 match_len = 0;
		for(j = cursor_start; j < cursor_end; j++){
			if(pData[i+match_len] == pData[j]){
				match_len++;
			}
			else{
				if(match_len >= MIN_MATCH_LEN && pCmpCp->l <= match_len){
					pCmpCp->p = cursor_start - i;
					pCmpCp->l = match_len;
					pCmpCp->c = pData[j];
				}
				break;
			}
		}

		if(j >= cursor_end && match_len >= MIN_MATCH_LEN && match_len >= pCmpCp->l){
			//my_printf("j = %d, cursor_start=%d, i=%d\n", j, cursor_start, i);
			pCmpCp->p = cursor_start - i;
			pCmpCp->l = match_len;
			if(j >= len)
				pCmpCp->c = '\0';
			else
				pCmpCp->c = pData[j];
		}
	}
	
	return;
}
#endif

void longest_match(uInt8 *pData, uInt32 len, uInt32 cursor, stLZ77CmpCp *pCmpCp)
{
	pCmpCp->p = 0;
	pCmpCp->l = 0;
	pCmpCp->c = pData[0];
	if(cursor == 0){
		return;
	}
	
	uInt32 cursor_start = cursor;
	uInt32 cursor_end = cursor_start + (((cursor + CUR_BUFF_LEN) <= len) ? CUR_BUFF_LEN : (len - cursor));
	uInt32 slide_start = (cursor > SLIDE_WIN_LEN) ? (cursor - SLIDE_WIN_LEN) : 0; 
	uInt32 i = slide_start, j = cursor_start;
	//my_printf("len= %d, cursor_start=%d, cursor_end=%d,slide_start=%d\n",
		//len, cursor_start, cursor_end, slide_start);
	for(; i < cursor; i++){ // slide window substring start index = i
		uInt32 match_len = 0;
		for(j = cursor_start; j < cursor_end; j++){
			if(pData[i+match_len] == pData[j]){
				match_len++;
			}
			else{
				if(pCmpCp->l <= match_len){
					pCmpCp->p = cursor_start - i;
					pCmpCp->l = match_len;
					pCmpCp->c = pData[j];
				}
				break;
			}
		}

		if(j >= cursor_end && match_len >= pCmpCp->l){
			//my_printf("j = %d, cursor_start=%d, i=%d\n", j, cursor_start, i);
			pCmpCp->p = cursor_start - i;
			pCmpCp->l = match_len;
			if(j >= len)
				pCmpCp->c = '\0';
			else
				pCmpCp->c = pData[j];
		}
	}
	
	return;
}

#if 0
static Int8 lz77_cmp_log[BLOCK_BYTES] = {'\0'};
#endif

void my_LZ77_compress(void *pSrcData, uInt32 len, vector<stLZ77CmpCp> *pCmpCpList)
{
	if(!pSrcData || !pCmpCpList)
		return;
	uInt8 *pData = (uInt8*)pSrcData;
	stLZ77CmpCp cmpCp;
	uInt32 cursor = 0, totalBytes = 0;
	//Int32 *pNext = new Int32[MAX_MATCH_LEN]();
	while(cursor < len)
	{
		#if USE_GOLOMB_ENCODE
		//longest_match_bf(pData, len, cursor, &cmpCp);
		//longest_match_kmp(pData, len, cursor, &cmpCp, pNext);
		longest_match_sunday(pData, len, cursor, &cmpCp);
		#else
		longest_match(pData, len, cursor, &cmpCp);
		#endif

		#if 0
		static uInt32 cnt = 0;
		if(totalBytes < (BLOCK_BYTES - 100)){
			uInt32 len = sprintf(&lz77_cmp_log[totalBytes], "[%d]cursor =%d,(p, l, c) = (%d, %d, %c)\n", cnt++, cursor, cmpCp.p, cmpCp.l, cmpCp.c);
			totalBytes += len;
		}
		#endif
	
		pCmpCpList->push_back(cmpCp);
		cursor += (cmpCp.l + 1);
	}

	#if 0
	FILE *pFd = NULL;
	pFd = fopen("./lz77_cmp_log.log", "wb");
	fwrite(lz77_cmp_log, totalBytes, 1, pFd);
	fclose(pFd);
	#endif
	//delete [] pNext;
	//pNext = NULL;
	return;
}

uInt32 my_LZ77_decompress(vector<stLZ77CmpCp> &cmpCpList, uInt8 *pOut)
{
	if(!pOut)
		return 0;
	uInt32 i = 0, j = 0, cur = 0;
	for(i = 0; i < cmpCpList.size(); i++){
		//printf("%d(p, l, c) = (%d, %d, %c)\n",i,cmpCpList[i].p, cmpCpList[i].l, cmpCpList[i].c);
		if(cmpCpList[i].l == 0 && cmpCpList[i].c != '\0'){
			pOut[cur++] = cmpCpList[i].c;
			continue;
		}
		
		for(j = 0; j < cmpCpList[i].l; j++){
			pOut[cur + j] = pOut[cur - cmpCpList[i].p + j];
		}
		cur += cmpCpList[i].l;
		pOut[cur++] = cmpCpList[i].c;
	}
	return cur;
}

/************** LZ78 编解码算法**********************/
//http://www.cnblogs.com/en-heng/p/6283282.html
#define USE_HASH_TABLE (1)

typedef struct
{
	uInt32 idx;    /* 单词在词典中的序号 */
	uInt8 *pSubStr; /* 记录单词在长串中的位置 */
	uInt32 len;    /* 单词的长度 */
}stDictionaryItem;

#pragma pack (1)
typedef struct
{
	uInt32 idx;
	uInt8   c;
}stLZ78CmpCp;
#pragma pack ()

#if USE_HASH_TABLE

uInt32 checkStrInDictionary(
	uInt8 *pData,
	uInt32 len,
	uInt32 curIdx,
	uInt32 key,
	enBool *pKeyRepeat,  /* 标识key 是否重复 */
	map<uInt32, vector<stDictionaryItem> > &dictHashMap)
{
	//printChar(pData, len);
	//my_printf("key = %d\n", key);
	map<uInt32, vector<stDictionaryItem> >::iterator it;
	it = dictHashMap.find(key);
	if(it != dictHashMap.end()){ /* 如果找到key */
		uInt16 i = 0;
		for(; i < it->second.size(); i++){
			//my_printf("[%d] len = %d\n", i, it->second[i].len);
			if((it->second[i].len == len) && 
				memcmp(it->second[i].pSubStr, pData, len * sizeof(uInt8)) == 0){
				//my_printf("len1=%d, len2=%d, idx = %d\n", it->second[i].len, len, it->second[i].idx);
				return it->second[i].idx;
			}
		}

		//my_printf("-----------\n");
	       /* 出现重复的key */
		stDictionaryItem item;
		item.idx = curIdx;
		item.pSubStr = pData;
		item.len = len;
		it->second.push_back(item);

		//my_printf("key = %d , it->second.size() = %d\n", key , it->second.size());
		*pKeyRepeat = TRUE;
		return 0;
	}

	*pKeyRepeat = FALSE;
	return 0;
}

// BKDR Hash Function
uInt32 BKDRHash(void *pStr, uInt32 len)
{
	uInt32 seed = 13131313; // 31 131 1313 13131 131313 etc..
	uInt32 hash = 0;

	uInt8 *pData = (uInt8*)pStr;
	uInt32 i = 0;
	for(; i < len; i++){
		hash = hash * seed + (pData[i] & 0xff);
	}

	return (hash & 0x7FFFFFFF);
}

// ELF Hash Function
uInt32 ELFHash(void *pStr, uInt32 len)
{
	uInt32 hash = 0;
	uInt32 x    = 0;

	uInt8 *pData = (uInt8*)pStr;
	uInt32 i = 0;
	for(; i < len; i++){
		hash = (hash << 4) + (pData[i] & 0xff);
		if ((x = hash & 0xF0000000L) != 0){
			hash ^= (x >> 24);
			hash &= ~x;
		}
	}

	return (hash & 0x7FFFFFFF);
}

void my_LZ78_compress(void *pSrcData, uInt32 len, vector<stLZ78CmpCp> *pCmpCpList)
{
	if(!pSrcData || !pCmpCpList)
		return;
	//uInt32 cntZero = 0;
	map<uInt32, vector<stDictionaryItem> > dictHashMap;

	uInt8 *pCur = (uInt8*)pSrcData;
	uInt32 cnt = 0;
	uInt32 dictIdx = 1;
	while(cnt < len)
	{
		stLZ78CmpCp cmpCp;
		uInt32 subLen = 1, preIdx = 0, curIdx = 0;
		uInt32 key = 0;
		enBool bKeyRepeat = FALSE;
		for(; subLen <= len - cnt; subLen++){
			key = BKDRHash(pCur, subLen);
			//key = ELFHash(pCur, subLen);
			if((curIdx = checkStrInDictionary(pCur, subLen, dictIdx, key, &bKeyRepeat, dictHashMap)) == 0){  /* 没在字典里找到子串 */
				break;
			}

			preIdx = curIdx;
		}
		
		if(curIdx != 0 && subLen > len - cnt){
			cmpCp.idx = curIdx;
			cmpCp.c = '\0';
			pCmpCpList->push_back(cmpCp);
			break;
		}
		else{
			//my_printf("@ key = %d, dictIdx= %d\n", key, dictIdx);
			if(bKeyRepeat == FALSE){
				stDictionaryItem item;
				item.idx = dictIdx;
				item.pSubStr = pCur;
				item.len = subLen;
				vector<stDictionaryItem> sameKeyList;
				sameKeyList.push_back(item);
				dictHashMap.insert(make_pair(key, sameKeyList));
			}
			++dictIdx;

			if(preIdx == 0){
				cmpCp.idx = 0;
				cmpCp.c = *pCur & 0xff;
			}
			else{
				cmpCp.idx = preIdx;
				cmpCp.c = *(pCur + subLen - 1) & 0xff;
			}

			pCmpCpList->push_back(cmpCp);

			
			//if(cmpCp.idx == 0)
			//	cntZero++;
			//my_printf("(idx=%d, c=%x)\n", cmpCp.idx, cmpCp.c);
			pCur += subLen;
			cnt += subLen;
		}
	}

	//my_printf("zero cnt = %d\n", cntZero);
	return;
}

uInt32 my_LZ78_decompress(vector<stLZ78CmpCp> &cmpCpList, uInt8 *pOut)
{
	if(!pOut)
		return 0;
	uInt8 *p = pOut;
	uInt32 i = 0, cur = 0;
	vector<stDictionaryItem> dic;
	stDictionaryItem item;
	for(i = 0; i < cmpCpList.size(); i++){
		item.idx = i + 1;
		item.pSubStr = NULL;
		item.len = 0;
		if(cmpCpList[i].idx == 0){
			item.pSubStr = p;
			item.len = 1;
			
			*p++ = cmpCpList[i].c & 0xff;
			dic.push_back(item);
			cur++;
			continue;
		}

		memcpy(p, dic[cmpCpList[i].idx - 1].pSubStr, dic[cmpCpList[i].idx - 1].len * sizeof(char));
		p[dic[cmpCpList[i].idx - 1].len] = cmpCpList[i].c & 0xff;
		
		item.pSubStr = p;
		item.len = dic[cmpCpList[i].idx - 1].len + 1;
		dic.push_back(item);

		p += item.len;
		cur += item.len;
	}
	return cur;
}

#else
/* if str in dictionary return index else return 0 */
uInt32 checkStrInDictionary(char *pStr, uInt32 len, vector<stDictionaryItem> &dic)
{
	char *p = pStr;
	//my_printf("dic.size()=%d\n", dic.size());
	uInt32 i = 0;
	for(; i < dic.size(); i++){
		if(dic[i].len == len){
			if(memcmp(p, dic[i].pSubStr, sizeof(char)* len) == 0)
				return dic[i].idx;
		}
	}

	return 0;
}

void my_LZ78_compress(void *pSrcData, uInt32 len, vector<stLZ78CmpCp> *pCmpCpList)
{
	if(!pSrcData || !pCmpCpList)
		return;
	vector<stDictionaryItem> dic;
	uInt8 *p = (uInt8*)pSrcData;
	uInt32 cur = 0;
	while(cur < len)
	{
		stDictionaryItem item;
		item.idx = 0;
		item.pSubStr = NULL;
		item.len = 0;

		stLZ78CmpCp cmpCp;
		uInt32 l = 1, preIdx = 0, curIdx = 0;
		for(; l <= len - cur; l++){
			if((curIdx = checkStrInDictionary(p, l, dic)) == 0)
				break;
			preIdx = curIdx;
		}

		//my_printf("preIdx=%d, curIdx=%d\n", preIdx, curIdx);
		if(curIdx != 0 && l > len - cur){
			cmpCp.idx = curIdx;
			cmpCp.c = '\0';
			pCmpCpList->push_back(cmpCp);
			break;
		}
		else{
			item.idx = dic.size() + 1;
			item.pSubStr = p;
			item.len = l;
		
			dic.push_back(item);

			if(preIdx == 0){
				cmpCp.idx = 0;
				cmpCp.c = *p;
			}
			else{
				cmpCp.idx = preIdx;
				cmpCp.c = *(p + l - 1);
			}

			pCmpCpList->push_back(cmpCp);
			//my_printf("(idx=%d, c=%c)\n", cmpCp.idx, cmpCp.c);
			p += l;
			cur += l;
		}
	}

	return;
}

uInt32 my_LZ78_decompress(vector<stLZ78CmpCp> &cmpCpList, uInt8 *pOut)
{
	if(!pOut)
		return 0;
	uInt8 *p = pOut;
	uInt32 i = 0, cur = 0;
	vector<stDictionaryItem> dic;
	stDictionaryItem item;
	for(i = 0; i < cmpCpList.size(); i++){
		item.idx = i + 1;
		item.pSubStr = NULL;
		item.len = 0;

		if(cmpCpList[i].idx == 0){
			item.pSubStr = p;
			item.len = 1;
			*p++ = cmpCpList[i].c & 0xff;
			dic.push_back(item);
			cur++;
			continue;
		}

		memcpy(p, dic[cmpCpList[i].idx - 1].pSubStr, dic[cmpCpList[i].idx - 1].len * sizeof(char));
		p[dic[cmpCpList[i].idx - 1].len] = cmpCpList[i].c & 0xff;
		
		item.pSubStr = p;
		item.len = dic[cmpCpList[i].idx - 1].len + 1;
		dic.push_back(item);

		p += item.len;
		cur += item.len;
	}
	return cur;
}
#endif


void print_lz77CmpCp(vector<stLZ77CmpCp> &cmpOutList, uInt32 needPrintNum, const char* fileName)
{
	uInt32 i = 0;
	if(needPrintNum > cmpOutList.size()){
		needPrintNum = cmpOutList.size();
	}
#if NEED_DUMP_DATA
	FILE *pFd = NULL;
	pFd = fopen(fileName, "wb");
#endif
	
	for(; i < needPrintNum; i++){
		my_printf("[%d] (p, l , c) = (%d, %d, %x)\n", i,
			cmpOutList[i].p, cmpOutList[i].l, cmpOutList[i].c);
		stLZ77CmpCp tmp = cmpOutList[i];
		#if NEED_DUMP_DATA
		fwrite(&tmp, sizeof(stLZ77CmpCp), 1, pFd);
		#endif
	}

#if NEED_DUMP_DATA
	fclose(pFd);
#endif
	return;
}

#if USE_GOLOMB_ENCODE /* 如果使用golomb 编码来存储 stLZ77CmpCp*/

uInt32 make_bitMap_table(vector<stLZ77CmpCp> &cmpOutList, uInt8 *pOut)
{
	uInt8 *pOutData = pOut;
	uInt32 bitPos = 0;
	uInt32 bitNums = cmpOutList.size();
	//uInt32 byteNums_mapTable = (bitNums % 8 == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	uInt32 byteNums_mapTable = (GET_MOD(bitNums, 8) == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);

	uInt8 *pBitMap = new uInt8[byteNums_mapTable]();

	my_warning("[BITMAP]Compress get map table byteNums = %d, cmpOutList.size()=%d\n",
		byteNums_mapTable, cmpOutList.size());

	bitPos = 0;
	while(bitPos < bitNums){
		if(cmpOutList[bitPos].l == 0){
			setBit_uInt8(pBitMap, bitPos);
		}
		bitPos++;
	}

	uInt32 huffmanEncodeBytes = 0;
	if(byteNums_mapTable > 1){
		/* 对bitMAP 表进行huffman 编码 */
		huffmanEncodeBytes = my_huffman_encode_char(pBitMap, byteNums_mapTable, pOutData);
		//pOutData += huffmanEncodeBytes;

		my_warning("<-1->[BITMAP]bitMap total Bytes = %d\n", byteNums_mapTable * sizeof(uInt8));
		my_warning("<-2->[BITMAP]=======use huffman encode bytes = %d\n", huffmanEncodeBytes);
	}
	else{
		memcpy(pOutData, pBitMap, byteNums_mapTable);
		//pOutData += byteNums_mapTable;
		huffmanEncodeBytes = byteNums_mapTable;
	}

	delete [] pBitMap;
	pBitMap = NULL;
	
	return huffmanEncodeBytes;
}

uInt32 my_compress_file_lz77(void *pData, uInt32 totalBytes, uInt8 *pOut)
{
	/* file struct:
		4 bytes("FLZ7") + 4 bytes mapLen + mapLen bits + compress Data
		map映射表储存compress输出的是匹配字串还是单个字符
		如果是单个字符用一位 1 表示 否则用0 表示。
	*/
	if(!pData || !pOut)
		return 0;
	uInt8 *pInData = (uInt8*)pData;
	uInt8 *pOutData = pOut;

	my_warning("(1)Start LZ77 compress....\n");
	Int32 ms = 0;
	ms = my_calc_process_time(NULL);
	vector<stLZ77CmpCp> cmpOutList;
	my_LZ77_compress(pInData, totalBytes, &cmpOutList);
	ms = my_calc_process_time(&ms);
	my_warning("[***TIME***] my_LZ77_compress() spend %d ms!!!\n", ms);

	print_lz77CmpCp(cmpOutList, cmpOutList.size(), "lz77cmpList_1.data");

	uInt32 cmpOutListSize = cmpOutList.size();
	memcpy(pOutData, &cmpOutListSize, sizeof(uInt32));
	pOutData += sizeof(uInt32);

	/* 对LZ77算法压缩的数据建立映射表，并用huffman对这个表进行编码 */
	my_warning("\n");
	my_warning("(2)Start make bitMap table....\n");
	uInt32 compressTotalBytes = 0;
	compressTotalBytes = make_bitMap_table(cmpOutList, pOutData);
	pOutData += compressTotalBytes;

	compressTotalBytes += sizeof(uInt32);

	uInt32 *pArry_p = new uInt32[cmpOutListSize]();
	vector<uInt32> pArry_l;
	uInt32 listIdx = 0, pCnt = 0;
	uInt8 *pSrcChar = new uInt8[cmpOutListSize]();
	for(listIdx = 0; listIdx < cmpOutListSize; listIdx++){
		if(cmpOutList[listIdx].l != 0){
			pArry_p[pCnt++] = cmpOutList[listIdx].p;
			pArry_l.push_back(cmpOutList[listIdx].l);
		}
		/* 保存c 值 */
		pSrcChar[listIdx] = cmpOutList[listIdx].c;
	}

	#if 1
	my_dump_data("./c_1.data", pSrcChar, cmpOutList.size());
	my_dump_data("./p_1.data", pArry_p, pCnt*sizeof(uInt32));
	uInt32 k = 0;
	uInt32 *pl = new uInt32[pCnt]();
	for(; k < pCnt; k++){
		pl[k] = pArry_l[k];
	}
	my_dump_data("./l_1.data", pl, pCnt*sizeof(uInt32));
	delete [] pl;
	pl = NULL;
	#endif
	my_warning("\n");
	my_warning("(3)Start huffman encode for cmpOutList.c ....\n");
	/* 对c 值进行huffman 编码 */
	uInt32 huffmanEncodeBytes = my_huffman_encode_char(pSrcChar, cmpOutListSize, pOutData);
	pOutData += huffmanEncodeBytes;
	compressTotalBytes += huffmanEncodeBytes;
	my_warning("<-1->===BEFORE===c total Bytes = %d\n",cmpOutListSize * sizeof(uInt8));
	my_warning("<-2->===AFTER====c huffman encode Bytes = %d\n", huffmanEncodeBytes);
	delete [] pSrcChar;
	pSrcChar = NULL;

	/* 保存l, p 有效的个数 */
	memcpy(pOutData, &pCnt, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	compressTotalBytes += sizeof(uInt32);
	/* 对p 进行合并 */
	my_warning("\n");
	my_warning("(4)Start combine_bits for cmpOutList.p ....\n");
	uInt32 num = (P_BITS * pCnt) / 8 + 1;
	uInt8 *pCmbOut = new uInt8[num]();
	combine_bits(pArry_p, pCnt, P_BITS, pCmbOut);

	my_warning("num = %d\n", num);

	my_warning("\n");
	my_warning("(5)Start huffman encode for combine_bits ....\n");
	static uInt8 f = 0;
	if(f == 0){
		my_dump_data("./Combine_p.data", pCmbOut, num);
		f = 1;
	}
	/* 对合并后的数据进行huffman编码 */
	huffmanEncodeBytes = my_huffman_encode_char(pCmbOut, num, pOutData);
	pOutData += huffmanEncodeBytes;
	compressTotalBytes += huffmanEncodeBytes;
	my_warning("<-1->===BEFORE===p combine after total Bytes = %d\n", sizeof(uInt8) * num);
	my_warning("<-2->===AFTER====p combine data huffman encode bytes = %d\n", huffmanEncodeBytes);

	delete [] pArry_p;
	pArry_p = NULL;
	delete [] pCmbOut;
	pCmbOut = NULL;
	my_warning("pCnt = %d;num = %d\n", pCnt, num);
	/* 对l 进行golomb 编码 */
	my_warning("\n");
	my_warning("(6)Start golomb_rice_encode for cmpOutList.l ....\n");
	vector<uInt32> lGolombCode;
	golomb_rice_encode(pArry_l, lGolombCode);

	uInt32 golombLen = lGolombCode.size();
	my_warning("golombLen = %d\n", golombLen);
	memcpy(pOutData, &golombLen, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	compressTotalBytes += sizeof(uInt32);

	uInt8 *pGolombCodeChar = new uInt8[golombLen*sizeof(uInt32)]();
	uInt8 *pGolombCodeCharHead = pGolombCodeChar;
	for(listIdx = 0; listIdx < lGolombCode.size(); listIdx++){
		uInt32 val = lGolombCode[listIdx];
		memcpy(pGolombCodeChar, &val, sizeof(uInt32));
		pGolombCodeChar += sizeof(uInt32);
	}
	
	huffmanEncodeBytes = my_huffman_encode_char(pGolombCodeCharHead, golombLen*sizeof(uInt32), pOutData);
	pOutData += huffmanEncodeBytes;

	delete [] pGolombCodeCharHead;
	pGolombCodeCharHead = NULL;

	compressTotalBytes += huffmanEncodeBytes;
	my_warning("<-1->===BEFORE===golomb encode total Bytes = %d\n", sizeof(uInt32) * lGolombCode.size());
	my_warning("<-2->===AFTER====l golomb encode ->huffman ecode bytes = %d\n", huffmanEncodeBytes);


	printf("After lz77 compress total bytes=%d, compress rate: %.2f%%\n",
		compressTotalBytes, (double)compressTotalBytes / totalBytes * 100);

	return compressTotalBytes;
}

uInt32 my_decompress_file_lz77(void *pData, uInt32 totalBytes, FILE* pFout)
{
	if(!pData || !pFout)
		return 0;
	Int32 decompressTotalBytes = 0;
	my_printf("It is use lz77 algorithm to decompress!\n");

	uInt8 *pInData = (uInt8*)pData;
	uInt32 bitNums = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	
	//uInt32 byteNums_mapTable = (bitNums % 8 == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	uInt32 byteNums_mapTable = (GET_MOD(bitNums, 8) == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	my_warning("bitNums = %d;byteNums_mapTable = %d\n",bitNums, byteNums_mapTable);

	/* 从huffman编码数据中反编码出bitMap映射表 */
	uInt8 *pBitMap = new uInt8[byteNums_mapTable]();
	uInt32 huffmanDecodeBytes = 0;
	if(byteNums_mapTable > 1){
		huffmanDecodeBytes = my_huffman_decode_char(pInData, pBitMap, byteNums_mapTable);
		pInData += huffmanDecodeBytes;
	}
	else{
		memcpy(pBitMap, pInData, byteNums_mapTable);
		pInData += byteNums_mapTable;
	}

	uInt8 *pChar = new uInt8[bitNums]();
	huffmanDecodeBytes = my_huffman_decode_char(pInData, pChar, bitNums);
	pInData += huffmanDecodeBytes;
	
	uInt32 pCnt = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	my_warning("pCnt = %d\n", pCnt);

	uInt32 num = (P_BITS * pCnt) / 8 + 1;
	uInt8 *pCmbData = new uInt8[num]();
	huffmanDecodeBytes = my_huffman_decode_char(pInData, pCmbData, num);
	pInData += huffmanDecodeBytes;

	my_warning("num = %d\n", num);

	uInt32 *pArry_p = new uInt32[pCnt](); //有效的p 数据
	decombine_bits(pCmbData, pCnt, P_BITS, pArry_p);
	delete [] pCmbData;
	pCmbData = NULL;

	uInt32 golombLen = *((uInt32*)pInData);
	my_warning("golombLen = %d\n", golombLen);
	pInData += sizeof(uInt32);

	uInt8 *pGolombCodeChar = new uInt8[golombLen * sizeof(uInt32)]();
	uInt8 *pGolombCodeCharHead = pGolombCodeChar;
	huffmanDecodeBytes = my_huffman_decode_char(pInData, pGolombCodeChar, golombLen * sizeof(uInt32));
	my_warning("huffmanDecodeBytes = %d\n", huffmanDecodeBytes);

	vector<uInt32> golombCode;
	uInt32 i = 0;
	for(; i < golombLen; i++){
		uInt32 code = *((uInt32*)pGolombCodeChar);
		pGolombCodeChar += sizeof(uInt32);
		golombCode.push_back(code);
	}

	delete [] pGolombCodeCharHead;
	pGolombCodeCharHead = NULL;

	vector<uInt32> pArry_l;
	golomb_rice_decode(golombCode, pArry_l, pCnt);
	my_warning("pArry_l.size() = %d\n", pArry_l.size());

	vector<stLZ77CmpCp> cmpOutList;
	uInt32 bitPos = 0, lpPos = 0;
	
	while(bitPos < bitNums){
		stLZ77CmpCp tmp;
		if(tstBit_uInt8(pBitMap, bitPos)){
			tmp.p = 0;
			tmp.l = 0;
			tmp.c = pChar[bitPos];
		}
		else{
			if(lpPos >= pCnt){
				my_error("Fatal Error!!!!!!!!!!!!");
				break;
			}
			tmp.p = pArry_p[lpPos];
			tmp.l = pArry_l[lpPos++];
			tmp.c = pChar[bitPos];
		}
		cmpOutList.push_back(tmp);
		bitPos++;
	}

	#if 1
	my_dump_data("./c_2.data", pChar, bitNums);
	my_dump_data("./p_2.data", pArry_p, pCnt*sizeof(uInt32));
	uInt32 k = 0;
	uInt32 *pl = new uInt32[pCnt]();
	for(; k < pCnt; k++){
		pl[k] = pArry_l[k];
	}
	my_dump_data("./l_2.data", pl, pCnt*sizeof(uInt32));
	delete [] pl;
	pl = NULL;
	#endif

	delete [] pArry_p;
	pArry_p = NULL;
	delete [] pChar;
	pChar = NULL;

	delete [] pBitMap;
	pBitMap = NULL;

	my_warning("Decompress get map tatle byteNums = %d, cmpOutList.size()=%d\n",
		byteNums_mapTable, cmpOutList.size());

	uInt32 cmpBeforeBytes = (BLOCK_BYTES + 8) & (~(sizeof(uInt32) - 1));
	uInt8 *pDecmpOutData = new uInt8[cmpBeforeBytes]();

	print_lz77CmpCp(cmpOutList, cmpOutList.size(), "lz77cmpList_2.data");
	
	decompressTotalBytes = 0;
	decompressTotalBytes = my_LZ77_decompress(cmpOutList, pDecmpOutData);

	#if !USE_GOLOMB_ENCODE
	if(pDecmpOutData[decompressTotalBytes - 1] == '\0'){
		decompressTotalBytes--;
	}
	#endif

	printf("decompressTotalBytes=%d\n", decompressTotalBytes);
	fwrite(pDecmpOutData, sizeof(uInt8) * decompressTotalBytes, 1, pFout);

	delete [] pDecmpOutData;
	pDecmpOutData = NULL;
	return decompressTotalBytes;
}

#else //#if NOUSE_GOLOMB_ENCODE

#define USE_HUFFMAN_ENCODE_CHAR (1)

/**********************************************************
压缩过程:
	假如源数据为:  abcdefg
	第一步压缩:  4 字节头+ 4字节bit 映射表的bit 个数+ 映射表数据
		+ cmpOutList数据(stLZ77CmpCp+1byte+1byte+stLZ77CmpCp+....这种格式, 
		前面的映射表就是用1和0 表示存储的是stLZ77CmpCp 还是1byte字符数据)
		
	如果定义NEED_COMPRESS_MAPTABLE 这个宏就是进一步对
		(4字节bit 映射表的bit 个数+ 映射表数据) 进行压缩
	第二步压缩: (4字节bit 映射表的bit 个数+ 映射表数据) 变为如下结构:
		(4字节bit 映射表的bit 个数+ 映射表数据+ cmpOutList数据) 
***********************************************************/
uInt32 make_bitMap_table(vector<stLZ77CmpCp> &cmpOutList, uInt8* pOut)
{
	uInt8 *pOutData = pOut;
	uInt32 listIdx = 0;
	uInt32 bitNums = cmpOutList.size();
	//uInt32 byteNums_mapTable = (bitNums % 8 == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	uInt32 byteNums_mapTable = (GET_MOD(bitNums, 8) == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);

	uInt8 *pTmpBitMap = NULL;
	byteNums_mapTable += sizeof(uInt32);
	uInt8 *pBitMap = new uInt8[byteNums_mapTable]();
	memcpy(pBitMap, &bitNums, sizeof(uInt32));
	pTmpBitMap = pBitMap + sizeof(uInt32);

	printf("(1)Compress get map table byteNums = %d, cmpOutList.size()=%d\n",
		byteNums_mapTable, cmpOutList.size());

	listIdx = 0;
	while(listIdx < bitNums){
		if(cmpOutList[listIdx].l == 0){
			setBit_uInt8(pTmpBitMap, listIdx);
		}
		listIdx++;
	}

	cout << "First bitMap total Bytes = " << byteNums_mapTable * sizeof(uInt8) << endl;

	/* 对MAP 表进行压缩 */
	vector<stLZ77CmpCp> mapCmpOutList;
	my_LZ77_compress(pBitMap, byteNums_mapTable, &mapCmpOutList);
	
	bitNums = mapCmpOutList.size();
	//byteNums_mapTable = (bitNums % 8 == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	byteNums_mapTable = (GET_MOD(bitNums, 8) == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	
	delete [] pBitMap;
	pBitMap = NULL;
	pBitMap = new uInt8[byteNums_mapTable]();
	
	listIdx = 0;
	printf("(2)Compress get compress map table byteNums = %d, mapCmpOutList.size()=%d\n",
		byteNums_mapTable, mapCmpOutList.size());

	while(listIdx < bitNums){
		if(mapCmpOutList[listIdx].l == 0){
			setBit_uInt8(pBitMap, listIdx);
		}
		listIdx++;
	}

	//fwrite(&bitNums, sizeof(uInt32), 1, pFout); // bitMap bitNums
	memcpy(pOutData, &bitNums, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	//fwrite(pBitMap, sizeof(uInt8) * byteNums_mapTable, 1, pFout);
	memcpy(pOutData, pBitMap, sizeof(uInt8) * byteNums_mapTable);
	pOutData += sizeof(uInt8) * byteNums_mapTable;
	cout << "=======second bitMap total Bytes = " << byteNums_mapTable * sizeof(uInt8) << endl;

	delete [] pBitMap;
	pBitMap = NULL;

	/* 写入压缩后的数据 */
	for(listIdx = 0; listIdx < mapCmpOutList.size(); listIdx++){
		if(mapCmpOutList[listIdx].l == 0){
			byteNums_mapTable += sizeof(uInt8);
			*pOutData = mapCmpOutList[listIdx].c;
			pOutData++;
		}
		else{
			byteNums_mapTable += sizeof(stLZ77CmpCp);
			*pOutData = (mapCmpOutList[listIdx].p & 0x1f) | ((mapCmpOutList[listIdx].l & 0x07) << 5);
			pOutData++;
			*pOutData = mapCmpOutList[listIdx].c;
			pOutData++;
		}
	}

	cout << "=======second (bitMap + mapCmpOutList) total Bytes = " << byteNums_mapTable * sizeof(uInt8) << endl;
	printf("(3)Compress get compress map table byteNums + dataNums = %d\n",
		byteNums_mapTable);
	
	return byteNums_mapTable + sizeof(uInt32);
}

uInt32 my_compress_file_lz77(void *pData, uInt32 totalBytes, uInt8 *pOut)
{
	/* file struct:
		4 bytes("FLZ7") + 4 bytes mapLen + mapLen bits + compress Data
		map映射表储存compress输出的是匹配字串还是单个字符
		如果是单个字符用一位 1 表示 否则用0 表示。
	*/
	if(!pData || !pOut)
		return 0;
	uInt8 *pInData = (uInt8*)pData;
	uInt8 *pOutData = pOut;
	
	vector<stLZ77CmpCp> cmpOutList;
	my_LZ77_compress(pInData, totalBytes, &cmpOutList);

	print_lz77CmpCp(cmpOutList, cmpOutList.size(), "./123.data");	

	/* 写入映射表 */
	uInt32 compressTotalBytes = 0;
	compressTotalBytes = make_bitMap_table(cmpOutList, pOutData);
	pOutData += compressTotalBytes;

	#if USE_HUFFMAN_ENCODE_CHAR
	uInt32 cmpOutListNum = cmpOutList.size();
	uInt8 *pTmp = pOutData;   //预留4字节存储lCnt
	pOutData += sizeof(uInt32);
	/* (1) 先存l和p的一个字节并统计字符c的权重 */
	uInt32 listIdx = 0;
	uInt32 pCharWeight[256] = {0}; /* 保存c 值重复的个数 */
	uInt32 lCnt = 0;
	for(listIdx = 0; listIdx < cmpOutListNum; listIdx++){
		pCharWeight[cmpOutList[listIdx].c & 0xff]++;
		if(cmpOutList[listIdx].l != 0){
			*pOutData = (cmpOutList[listIdx].p & 0x1f) | ((cmpOutList[listIdx].l & 0x07) << 5);
			pOutData++;
			lCnt++;
		}
	}

	memcpy(pTmp, &lCnt, sizeof(uInt32));
	compressTotalBytes += (sizeof(uInt8) * lCnt);
	printf("lCnt = %d, cmpOutListNum = %d\n", lCnt, cmpOutListNum);
	cout << "=======l and p total Bytes = " << lCnt * sizeof(uInt8) << endl;

	/* (2) 为c 元素建立huffman树 */
	cout << "start create pCharHuffmanTree:" << endl;
	stHuffmanTreeNode *pCharHuffmanTree = NULL;
	uInt32 realLeafNum = 0;
	pCharHuffmanTree = create_huffman_tree(pCharWeight, 256, &realLeafNum);
	printf("pCharHuffmanTree realLeafNum = %d\n", realLeafNum); 

	uInt32 j = 0;
	my_printf("pCharHuffmanTree as follow:\n");
	for(j = 0; j < 256*2-1; j++){
		if(pCharHuffmanTree[j].weight == 0 && pCharHuffmanTree[j].parent == 0 &&
			pCharHuffmanTree[j].leftChild == 0 && pCharHuffmanTree[j].rightChild == 0){
			continue;
		}
		my_printf("[w, p, l, r]=%d:[%d, %d, %d, %d]\n",j,pCharHuffmanTree[j].weight, \
			pCharHuffmanTree[j].parent, pCharHuffmanTree[j].leftChild, pCharHuffmanTree[j].rightChild);
	}

	/* (3) pCharHuffmanTree树简化, 建立映射表并保存 */
	cout << "start simpfy pCharHuffmanTree and save:" << endl;
	uInt8 charSimpleHuffmanTreeSize = 0;
	if(realLeafNum > 1){
		charSimpleHuffmanTreeSize = (realLeafNum - 1) & 0xff;
	}
	else{
		charSimpleHuffmanTreeSize = 0;
	}
	printf("charSimpleHuffmanTreeSize = %d\n", charSimpleHuffmanTreeSize);
	stHuffmanTreeNodeCharSimple *pCharHuffmanTreeSimple = new stHuffmanTreeNodeCharSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimple, NULL);

	uInt8 bitMapNum = (charSimpleHuffmanTreeSize*2) / 8; //左右节点的index都需要映射
	//bitMapNum = ((charSimpleHuffmanTreeSize*2) % 8 == 0) ? bitMapNum : (bitMapNum+1);
	bitMapNum = (GET_MOD(charSimpleHuffmanTreeSize*2, 8) == 0) ? bitMapNum : bitMapNum + 1;
	uInt8 pCharHuffmanTreeBitMap[64] = {0}; 

	uInt16 bitPos = 0;
	for(j = 0; j < charSimpleHuffmanTreeSize; j++){
		uInt32 leftChildIdx = pCharHuffmanTree[j + 256+(256-realLeafNum)].leftChild;
		uInt32 rightChildIdx = pCharHuffmanTree[j + 256+(256-realLeafNum)].rightChild;
		if(leftChildIdx >= 256){
			setBit_uInt8(pCharHuffmanTreeBitMap, bitPos++); //如果大于叶子节点的个数则需要映射
			pCharHuffmanTreeSimple[j].leftChild = (leftChildIdx - 256) & 0xff;
		}
		else{
			pCharHuffmanTreeSimple[j].leftChild = leftChildIdx & 0xff;
			bitPos++;
		}

		if(rightChildIdx >= 256){
			setBit_uInt8(pCharHuffmanTreeBitMap, bitPos++); //如果大于叶子节点的个数则需要映射
			pCharHuffmanTreeSimple[j].rightChild = (rightChildIdx - 256)  & 0xff;
		}
		else{
			pCharHuffmanTreeSimple[j].rightChild = rightChildIdx & 0xff;
			bitPos++;
		}
	}

	//fwrite(&charSimpleHuffmanTreeSize, sizeof(uInt8), 1, pFout); //这个值不会超过256所以一个字节就可以了
	memcpy(pOutData, &charSimpleHuffmanTreeSize, sizeof(uInt8));
	pOutData += sizeof(uInt8);
	compressTotalBytes += sizeof(uInt8);
	//fwrite(pCharHuffmanTreeBitMap, sizeof(uInt8) * bitMapNum, 1, pFout); //写入映射表
	memcpy(pOutData, pCharHuffmanTreeBitMap, sizeof(uInt8) * bitMapNum);
	pOutData += sizeof(uInt8) * bitMapNum;
	compressTotalBytes += sizeof(uInt8) * bitMapNum;
	cout << "=======pCharHuffmanTreeSimple BitMap total bytes = " << sizeof(uInt8) * bitMapNum << endl;
	//fwrite(pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple), 1, pFout);
	memcpy(pOutData, pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	pOutData += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);
	compressTotalBytes += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);
	
	delete [] pCharHuffmanTreeSimple;
	pCharHuffmanTreeSimple = NULL;
	cout << "=======pCharHuffmanTreeSimple tree total bytes = " << charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple) << endl;

	/* (4) 对char 进行huffman 编码 */
	cout << " start huffman encode for char:" << endl;
	vector<uInt32> charHuffmanCode;
	uInt8 *pAllCmpListChar = new uInt8[cmpOutListNum](); //保存原来的c 值
	ASSERT_RELEASE((void*)pAllCmpListChar, NULL);
	for(j = 0; j < cmpOutListNum; j++){
		pAllCmpListChar[j] = cmpOutList[j].c & 0xff;
	}
	huffman_encode_char(pAllCmpListChar, cmpOutListNum, pCharHuffmanTree, 256, charHuffmanCode);

	delete [] pAllCmpListChar;
	pAllCmpListChar = NULL;
	
	uInt32 *pCharHuffmanCode = new uInt32[charHuffmanCode.size()]();
	ASSERT_RELEASE((void*)pCharHuffmanCode, NULL);
	for(j = 0; j < charHuffmanCode.size(); j++){
		pCharHuffmanCode[j] = charHuffmanCode[j];
	}
	memcpy(pOutData, &j, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	compressTotalBytes += sizeof(uInt32);
	memcpy(pOutData, pCharHuffmanCode, sizeof(uInt32) * j);
	pOutData += sizeof(uInt32) * j;
	compressTotalBytes += j * sizeof(uInt32);

	delete [] pCharHuffmanCode;
	pCharHuffmanCode = NULL;
	delete [] pCharHuffmanTree;
	pCharHuffmanTree = NULL;
	cout << "=======pCharHuffmanCode bytes = " << j * sizeof(uInt32) << endl;

	#else
	/* 写入压缩后的数据 */
	uInt32 listIdx = 0;
	for(listIdx = 0; listIdx < cmpOutList.size(); listIdx++){
		if(cmpOutList[listIdx].l == 0){
			*pOutData = cmpOutList[listIdx].c;
			pOutData++;
			compressTotalBytes += sizeof(uInt8);
		}
		else{
			*pOutData = (cmpOutList[listIdx].p & 0x1f) | ((cmpOutList[listIdx].l & 0x07) << 5);
			pOutData++;
			*pOutData = cmpOutList[listIdx].c;
			pOutData++;
			compressTotalBytes += sizeof(stLZ77CmpCp);
		}
	}
	#endif
	printf("After lz77 compress total bytes=%d, compress rate: %.2f%%\n",
		compressTotalBytes, (double)compressTotalBytes / totalBytes * 100);
	return compressTotalBytes;
}

uInt32 my_decompress_file_lz77(void *pData, uInt32 totalBytes, FILE* pFout)
{
	if(!pData || !pFout)
		return 0;
	Int32 decompressTotalBytes = 0;
	my_printf("It is use lz77 algorithm to decompress!\n");

	uInt8 *pInData = (uInt8*)pData;
	uInt32 bitNums = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	totalBytes -= sizeof(uInt32);
	
	//uInt32 byteNums_mapTable = (bitNums % 8 == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	uInt32 byteNums_mapTable = (GET_MOD(bitNums, 8) == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);

	/* 4字节位个数+ n字节的位信息+m字节位信息map的数据 */
	/* 先解压map Table 数据 */
	vector<stLZ77CmpCp> cmpOutList;
	uInt32 i = byteNums_mapTable;
	uInt32 bitMap_idx  = 0;
	uInt8 *pBitMap = new uInt8[byteNums_mapTable]();
	memcpy(pBitMap, pInData, byteNums_mapTable * sizeof(uInt8));
	pInData += byteNums_mapTable * sizeof(uInt8);
	uInt32 bitPos = 0, dataPos = 0;
	while(bitPos < bitNums){
		stLZ77CmpCp tmp;
		if(tstBit_uInt8(pBitMap, bitPos)){
			tmp.p = 0;
			tmp.l = 0;
			tmp.c = pInData[dataPos];
		}
		else{
			tmp.p = pInData[dataPos] & 0x1f;
			tmp.l = (pInData[dataPos] & 0xe0) >> 5;
			tmp.c = (uInt8)pInData[++dataPos];
		}
		cmpOutList.push_back(tmp);
		bitPos++;
		dataPos++;
	}

	delete [] pBitMap;
	pBitMap = NULL;

	pInData += dataPos * sizeof(uInt8);

	/* 至此i 的值为压缩map表之前，真正的数据段开始的索引 */

	decompressTotalBytes = 0;
	uInt8 *pMapTableOut = new uInt8[cmpOutList.size() * (CUR_BUFF_LEN+1)]();
	uInt8 *pMapTableOutHead = pMapTableOut;
	if(pMapTableOut == NULL){
		cout << "pMapTableOut is NULL!" << endl;
		return 0;
	}
	decompressTotalBytes = my_LZ77_decompress(cmpOutList, (uInt8*)pMapTableOut);
	
	if(pMapTableOut[decompressTotalBytes - 1] == '\0'){
		decompressTotalBytes--;
	}

	/* pMapTableOut 保存的信息为:  4 bytes bitNums + bitNums 个bit位的字节数据 */
	/* 解析解码后的MAP TABLE */
	bitNums = *((uInt32*)pMapTableOut);
	pMapTableOut += sizeof(uInt32);

	//byteNums_mapTable = (bitNums % 8 == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);
	byteNums_mapTable = (GET_MOD(bitNums, 8) == 0) ? (bitNums / 8) : ((bitNums / 8) + 1);

	cmpOutList.clear();
	bitMap_idx  = 0;
	
	#if USE_HUFFMAN_ENCODE_CHAR
	uInt32 cmpOutListNum = bitNums;
	uInt32 lCnt = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	printf("lCnt = %d, cmpOutListNum=%d\n",lCnt, cmpOutListNum); 

	uInt8 *pLP = new uInt8[lCnt]();
	memcpy(pLP, pInData, sizeof(uInt8) * lCnt);
	pInData += sizeof(uInt8) * lCnt;

	/* 解压char 部分 */
	uInt8 charSimpleHuffmanTreeSize = (uInt8)*pInData;
	pInData++;
	printf("charSimpleHuffmanTreeSize = %d\n" ,charSimpleHuffmanTreeSize);

	/* 获得char 的简单huffman树 */
	stHuffmanTreeNodeSimple *pCharHuffmanTreeSimple = new stHuffmanTreeNodeSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimple, NULL);
	stHuffmanTreeNodeCharSimple *pCharHuffmanTreeSimpleTmp = new stHuffmanTreeNodeCharSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimpleTmp, pCharHuffmanTreeSimple, NULL);

	uInt8 bitMapNum = (charSimpleHuffmanTreeSize*2) / 8; //左右节点的index都需要映射
	//bitMapNum = ((charSimpleHuffmanTreeSize*2) % 8 == 0) ? bitMapNum : (bitMapNum+1);
	bitMapNum = (GET_MOD(charSimpleHuffmanTreeSize*2, 8) == 0) ? bitMapNum : (bitMapNum+1);
	uInt8 pCharHuffmanTreeBitMap[64] = {0}; //最大64 = 256 * 2 /8

	memcpy(pCharHuffmanTreeBitMap, pInData, sizeof(uInt8) * bitMapNum); //获取映射表数据
	pInData += sizeof(uInt8) * bitMapNum;
	memcpy(pCharHuffmanTreeSimpleTmp, pInData, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	pInData += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);

	bitPos = 0;
	for(i = 0; i < charSimpleHuffmanTreeSize; i++){
		enBool isMap = FALSE;
		isMap = tstBit_uInt8(pCharHuffmanTreeBitMap, bitPos++);
		if(isMap){
			pCharHuffmanTreeSimple[i].leftChild = pCharHuffmanTreeSimpleTmp[i].leftChild + 256;
		}
		else{
			pCharHuffmanTreeSimple[i].leftChild = pCharHuffmanTreeSimpleTmp[i].leftChild;
		}
		isMap = tstBit_uInt8(pCharHuffmanTreeBitMap, bitPos++);
		if(isMap){
			pCharHuffmanTreeSimple[i].rightChild = pCharHuffmanTreeSimpleTmp[i].rightChild + 256;
		}
		else{
			pCharHuffmanTreeSimple[i].rightChild = pCharHuffmanTreeSimpleTmp[i].rightChild;
		}
	}

	delete [] pCharHuffmanTreeSimpleTmp;
	pCharHuffmanTreeSimpleTmp = NULL;

	/* 获得char 的huffman编码uInt32 的个数 */
	uInt32 charHuffmanCodeNums = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	cout << "charHuffmanCodeBytes = " << charHuffmanCodeNums * sizeof(uInt32) << endl;

	vector<uInt32> charHuffmanCode;
	for(i = 0; i < charHuffmanCodeNums; i++){
		uInt32 codeValue = *((uInt32*)pInData);
		charHuffmanCode.push_back(codeValue);
		pInData += sizeof(uInt32);
	}

	uInt8 *pAllCmpListChar = new uInt8[cmpOutListNum]();
	ASSERT_RELEASE((void*)pAllCmpListChar, pCharHuffmanTreeSimple, NULL);
	huffman_decode_char(pCharHuffmanTreeSimple, 
						charHuffmanCode,
						pAllCmpListChar,
						cmpOutListNum,
						256,
						charSimpleHuffmanTreeSize+1); //实际的叶子节点数比简单huffman数组个数多一个

	delete [] pCharHuffmanTreeSimple;
	pCharHuffmanTreeSimple = NULL;

	bitPos = 0;
	uInt32 plPos = 0;
	while(bitPos < bitNums){
		stLZ77CmpCp tmp;
		if(tstBit_uInt8(pMapTableOut, bitPos)){
			tmp.p = 0;
			tmp.l = 0;
			tmp.c = pAllCmpListChar[bitPos];
		}
		else{
			tmp.p = pLP[plPos] & 0x1f;
			tmp.l = (pLP[plPos++] & 0xe0) >> 5;
			tmp.c = pAllCmpListChar[bitPos];
		}
		cmpOutList.push_back(tmp);
		bitPos++;
	}

	delete [] pLP;
	pLP = NULL;
	delete [] pAllCmpListChar;
	pAllCmpListChar = NULL;
	
	#else //#if USE_HUFFMAN_ENCODE_CHAR

	bitPos = 0, dataPos = 0;
	while(bitPos < bitNums){
		stLZ77CmpCp tmp;
		if(tstBit_uInt8(pMapTableOut, bitPos)){
			tmp.p = 0;
			tmp.l = 0;
			tmp.c = pInData[dataPos];
		}
		else{
			tmp.p = pInData[dataPos] & 0x1f;
			tmp.l = (pInData[dataPos] & 0xe0) >> 5;
			tmp.c = (uInt8)pInData[++dataPos];
		}
		cmpOutList.push_back(tmp);
		bitPos++;
		dataPos++;
	}
	#endif

	delete [] pMapTableOutHead;
	pMapTableOutHead = NULL;
	printf("Decompress get map tatle byteNums = %d, cmpOutList.size()=%d\n",
		byteNums_mapTable  + 4, cmpOutList.size());

	uInt32 cmpBeforeBytes = (BLOCK_BYTES + 8) & (~(sizeof(uInt32) - 1));
	uInt8 *pDecmpOutData = new uInt8[cmpBeforeBytes]();
	
	decompressTotalBytes = 0;
	decompressTotalBytes = my_LZ77_decompress(cmpOutList, pDecmpOutData);

	print_lz77CmpCp(cmpOutList, cmpOutList.size(), "./456.data");
	
	if(pDecmpOutData[decompressTotalBytes - 1] == '\0'){
		decompressTotalBytes--;
	}
	printf("decompressTotalBytes=%d\n", decompressTotalBytes);
	fwrite(pDecmpOutData, sizeof(uInt8) * decompressTotalBytes, 1, pFout);

	delete [] pDecmpOutData;
	pDecmpOutData = NULL;
	return decompressTotalBytes;
}
#endif

void Merge(vector<stLZ78CmpCp> &arr, uInt32 low, uInt32 mid, uInt32 high)
{
	//将两个有序区归并为一个有序区
	uInt32 i = low, j = mid + 1, k = 0;
	stLZ78CmpCp *temp = new stLZ78CmpCp[high-low+1];
	while(i <= mid && j <= high)
	{
		if(arr[i].idx <= arr[j].idx)
			temp[k++] = arr[i++];
		else
			temp[k++] = arr[j++];
	}
	while(i <= mid) temp[k++] = arr[i++];
	while(j <= high) temp[k++] = arr[j++];
	for(i = low, k=0; i <= high; i++, k++)
		arr[i] = temp[k];
	delete []temp;
}

/* 二路归并排序: Average: O(nlog2n), Best: O(nlog2n), Worst: O(nlog2n) */
void my_merge_sort_lz78CmpCp(vector<stLZ78CmpCp> &arr, uInt32 n)//参数和递归略不同， n 代表数组中元素个数，即数组最大下标是 n-1
{
	int size = 1, low, mid, high;
	while(size <= n-1)
	{
		low = 0;
		while(low+size <= n-1)
		{
			mid = low + size-1;
			high = mid + size;
			if(high > n - 1)//第二个序列个数不足 size
				high = n - 1;
			Merge(arr,low, mid, high);//调用归并子函数
			low = high + 1;//下一次归并时第一关序列的下界
		}
		size *= 2;//范围扩大一倍
	}
}

void huffman_encode_idxGroup(
	uInt32 *pIdxInWhichGroup, //需要编码的idx所在的group, pIdxInWhichGroup保存的group值就是叶子节点的index
	uInt32 groupCnt, 
	stHuffmanTreeNode *pHuffmanTree, // 已经创建好的huffman树
	uInt32 leafNum,                        // huffman树叶子节点个数
	vector<uInt32> &outCode)         //输出的huffman编码
{
	if(!pHuffmanTree || !pIdxInWhichGroup)
		return;
	if(leafNum <= 1)
		return;

	uInt8 *pCode = new uInt8[leafNum]();
	uInt32 nodeMaxNum = 2 * leafNum - 1;

	uInt8 bitCnt = 0;
	bitset<BIT_NUMS> oneItem;
	oneItem.reset();
	uInt32 i = 0;
	/* 遍历pIdxInWhichGroup  */
	for(; i < groupCnt; i++){
		/* 从叶子节点开始逆向获得编码 */
		uInt32 start = leafNum - 1;
		uInt32 leafIndx = pIdxInWhichGroup[i];
		
		/* check一下是真的叶子节点 */
		if((pHuffmanTree[leafIndx].leftChild == 0) && (pHuffmanTree[leafIndx].rightChild == 0)){
			uInt32 parentIdx = pHuffmanTree[leafIndx].parent;
			uInt32 curIdx = leafIndx;
			while((parentIdx < nodeMaxNum) && (parentIdx != 0)){
				/* 如果当前节点是父节点的左孩子 */
				if(pHuffmanTree[parentIdx].leftChild == curIdx){
					pCode[start--] = '0';
					//cout << " " << 0;
				}
				else{
					pCode[start--] = '1';
					//cout << " " << 1;
				}

				curIdx = parentIdx;
				parentIdx = pHuffmanTree[parentIdx].parent;
			}
		}

		//printf("(%d,%d)%d huffman code is: ",start, leafNum, pIdxInWhichGroup[i]);
		uInt32 j = start + 1;
		for(; j < leafNum; j++){
			//my_printf("%c ", pCode[j]);
			if(bitCnt >= BIT_NUMS){
				//cout << endl;
				bitCnt = 0;
				//cout << "encodeBits = " << oneItem << endl;
				outCode.push_back(oneItem.to_ulong());
				oneItem.reset();
			}

			if(pCode[j] == '1'){
				oneItem.set(bitCnt++);
				//cout << " " << 1;
			}
			else{
				oneItem.reset(bitCnt++);
				//cout << " " << 0;
			}
		}

		//cout << endl;
	}

	if(bitCnt != 0){
		bitCnt = 0;
		//cout << "encodeBits = " << oneItem << endl;
		outCode.push_back(oneItem.to_ulong());
		oneItem.reset();
	}
	
	delete [] pCode;
	return;
}

/* 由于组编码实际的leafNum和权重不为0的个数是一样的 */
void huffman_decode_idxGroup(
	stHuffmanTreeNodeSimple *pHuffmanTree,
	vector<uInt32> &huffmanCode,
	uInt32 *pTreeIndex,
	uInt32 totalCnt,
	uInt32 leafNum)  
{
	if(!pHuffmanTree || !pTreeIndex)
		return;
	if(leafNum <= 1)
		return;
	uInt32 i = 0, j = 0;
	uInt32 m = leafNum - 1; // n 个叶子节点，有n - 1个节点
	uInt32 start = m - 1;
	//printf("huffmanCode.size() = %d\n", huffmanCode.size());
	for(; i < huffmanCode.size(); i++){
		uInt32 code = huffmanCode[i];
		//printf("code = %x\n", huffmanCode[i]);
		uInt8 bitCnt = 0;
		while(bitCnt < BIT_NUMS){
			uInt8 bit = code & 0x01;
			if(bit == 0){
				//cout << " " << 0;
				start = pHuffmanTree[start].leftChild;
			}else{
				//cout << " " << 1;
				start = pHuffmanTree[start].rightChild;
			}

			code >>= 1;
			bitCnt++;
			
			if(start < leafNum){ // start 的值为0 ~ n-1则为叶子节点
				//cout << " j = " << j << endl;
				pTreeIndex[j++] = start;
				start = m - 1;
				if(j >= totalCnt)
					return;
			}
			else{
				start -= leafNum;
			}
		}
	}
	return;
}

/******************************************
(1)没有用huffman编码，那么存储的信息就是
	vector<stLZ78CmpCp> cmpOutList 数组的内容；
(2)使用huffman编码:、
	1: cmpOutList 数组( idx, c) 按idx 排序。
	2: 将排序后的idx检索，将idx按小到大放入pIndx数组(无重复)
		得到idx的个数为wCnt
	3: 位了减小存储的信息，可以将pIndx[wCnt]中的wCnt个
		idx值用位图进行压缩(bitMap), 压缩的byte 个数为
		(idx的最大值/ 8) + 1 个;
	4: 为pIndx数组的idx值为数组下标建立map映射表mapIdx
	5:   将pIndex按每组256个进行分组
		由于pIndex是排好序的，里面存储的idx值按升序排序。
		比如: pIndex数组内容为:
				0      0
				1      3
				2      4
				3      5
				4      7
		假如cmpOutList[0].idx 的值为5，那么它映射到pIndex的序号应该是
		3， 3按分组为Group 0, 且在group 0 的第4号位置
		创建数组groupCnt[]用于统计cmpOutList[].idx分别出现在group的个数
		groupCnt[i]分别得到idx出现在group i的频率。

	6:	然后用groupCnt[i]作为权重数组，建立huffman树。
		假如group 0的huffman 编码为: 1 0  (组的huffman编码bit个数m = log2(groupNum))
		那么cmpOutList[0].idx = 5就可以表示为: 10 0000 0011 (组号+ 组内序号)
		用一个字节就够来表示组内序号因为一组为256个数
		(用0x00 ~ 0xff表示)
		这样节省了很多空间，原来需要4个字节存储idx值现在只需
		组的huffman编码bit位+ 1个字节来表示idx。
		注:  如果用原来的3字节来作为组的huffman编码, 24个bit 可以编码
		2的24次方个组= 16777216，16777216 * 256 = 4294967296 (2^32) 达到uInt32表示
		范围的极限，因此这种方法可以有效的减小对idx的存储
	7:   对每个idx 在哪个组pInWhichGroup[] 进行huffman编码
	6: 解决完idx的储存，现在需要解决c的存储，先建个256大小的数组，统计
	    下每个c重复的个数，保存到pChar数组pchar[0] 的值为c = 0x00 重复的次数。  
	8: 写入每个idx 在各自的组中的位置信息pInGroupPos
	9: 为pChar建立huffman树，huffman树大小为2*256-1个单元
	10: 将huffman树转换为简单的huffman树(stHuffmanTreeNodeSimple)，并存储
	    256-1个单元。
	11: 为数组cmpOutList[i].c 获取huffman编码并存储
	    
*******************************************/

/* 做第2 步和第6 步 */
uInt32 filter_idx_and_char(
	vector<stLZ78CmpCp> &cmpOutList,
	uInt32 *pIndex,
	uInt32 *pChar)
{
	uInt8 c = (uInt8)(cmpOutList[0].c & 0xff);
	pChar[c]++;
	uInt32 wCnt = 0;  //统计idx 的个数
	uInt32 idxTmp = cmpOutList[0].idx;
	pIndex[wCnt++] = cmpOutList[0].idx;
	uInt32 j = 0;
	for(j = 1; j < cmpOutList.size(); j++){
		uInt8 c = (uInt8)(cmpOutList[j].c & 0xff);
		pChar[c]++;
		if(idxTmp == cmpOutList[j].idx)
			continue;
		else{
			pIndex[wCnt++] = cmpOutList[j].idx; //保存idx的值
			idxTmp = cmpOutList[j].idx;
		}
	}

	return wCnt;
}

uInt32 my_compress_file_lz78(void *pData, uInt32 totalBytes, uInt8 *pOut)
{
	if(!pData || !pOut)
		return 0;

	uInt8 *pInData = (uInt8*)pData;
	uInt8 *pOutData = pOut;
	vector<stLZ78CmpCp> cmpOutList;
	uInt32 compressTotalBytes = 0;

	#if NEED_DUMP_DATA
	FILE *pFd = NULL;
	#endif
	
	my_LZ78_compress(pInData, totalBytes, &cmpOutList);
	printf("cmpOutList.size() = %d\n", cmpOutList.size());

	uInt32 j = 0;
	//vector<stLZ78CmpCp> cmpOutList_tmp(cmpOutList);
	uInt32 cmpOutListNum = cmpOutList.size();

	uInt32 *pAllCmpListIdx = new uInt32[cmpOutListNum]();
	ASSERT_RELEASE((void*)pAllCmpListIdx, NULL);
	uInt8 *pAllCmpListChar = new uInt8[cmpOutListNum](); //保存原来的c 值
	ASSERT_RELEASE((void*)pAllCmpListChar, pAllCmpListIdx, NULL);
	for(j = 0; j < cmpOutListNum; j++){
		pAllCmpListIdx[j] = cmpOutList[j].idx;
		pAllCmpListChar[j] = cmpOutList[j].c & 0xff;
	}
	
	my_dump_data("./pAllCmpListIdx_1.data", pAllCmpListIdx, sizeof(uInt32)*cmpOutListNum);
	my_dump_data("./pCmpListChar_1.data", pAllCmpListChar, cmpOutListNum*sizeof(uInt8));
	
	/* (1) 按idx 排序 */
	cout << "(1) start sort idx:" << endl;
	my_merge_sort_lz78CmpCp(cmpOutList, cmpOutListNum);
	
	my_printf("compress result:\n");
	for(j = 0; j < cmpOutListNum; j++){
		my_printf("@@[%d] idx: %d; c = %c\n", j, cmpOutList[j].idx, cmpOutList[j].c);
	}

	/* (2)  将排序后的idx检索，将idx按小到大放入pIndx数组(无重复) */
	cout << "(2) start save idx no repeat nums and count char:" << endl;
	uInt32 *pIndex = new uInt32[cmpOutListNum](); /* 将排序的idx 存入数组 */
	uInt32 pCharWeight[256] = {0}; /* 保存c 值重复的个数 */
	ASSERT_RELEASE((void*)pCharWeight, pIndex, NULL);
	uInt32 wCnt = 0;  //统计idx 的个数
	wCnt = filter_idx_and_char(cmpOutList, pIndex, pCharWeight);
	cout << "wCnt = " << wCnt  << endl;

	my_dump_data("./pIndex_1.data", pIndex,  sizeof(uInt32)*wCnt);
	
	/* (3) 用bit map 方法对pIndex保存的idx进行压缩*/
	cout << "(3) start compress pIndex by bitMap:" << endl;
	uInt32 idxBitMapNums = pIndex[wCnt-1] / 8; //用最大的idx值/ 8即为所需uInt8的个数
	idxBitMapNums += 1; //要多用一位, 比如8就要存在第二个字节上了
	printf("The max idx = %d, need %d uInt8 to do bitMap\n", pIndex[wCnt-1], idxBitMapNums);

	uInt8 *pIdxBitMap = new uInt8[idxBitMapNums]();
	ASSERT_RELEASE((void*)pIdxBitMap, pIndex, pCharWeight, NULL);
	for(j = 0; j < wCnt; j++){
		setBit_uInt8(pIdxBitMap, pIndex[j]);
		//cout << pIndex[j] << endl;
	}

	/* 先写入4 字节pIndex 表不重复idx 的个数 */
	/* 再写入idx 用bitMap压缩后的数据 */
	
	/* bitMap 之所以只保存wCnt 就够了，是因为解码的时候
	    可以挨个bit进行统计只要统计个数为wCnt 就说明已经
	    把bitMap表解压出来了*/
	compressTotalBytes += sizeof(uInt32);
	//fwrite(&wCnt, sizeof(uInt32), 1, pFout);
	memcpy(pOutData, &wCnt, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	compressTotalBytes += idxBitMapNums * sizeof(uInt8);
	//fwrite(pIdxBitMap, idxBitMapNums * sizeof(uInt32), 1, pFout);
	memcpy(pOutData, pIdxBitMap, idxBitMapNums * sizeof(uInt8));
	pOutData += idxBitMapNums * sizeof(uInt8);

	my_dump_data("./pIdxBitMap_1.data", pIdxBitMap, idxBitMapNums * sizeof(uInt8));

	delete [] pIdxBitMap;
	pIdxBitMap = NULL;
	cout << "=======bitMap total Bytes = " << idxBitMapNums * sizeof(uInt8) << endl;
	
	/* (4) 建立idx值到pIndex数组索引的映射 */
	cout << "(4) start create idx map to index of pIndx table:" << endl;
	map<uInt32, uInt32> mapIdx;
	for(j = 0; j < wCnt; j++){
		mapIdx.insert(make_pair(pIndex[j], j));
	}
	
	delete [] pIndex;
	pIndex = NULL;

	/*(5)  将pIndex按每组256个进行分组*/
	cout << "(5) start map cmpOutList table idxs to pIndx table:" << endl;
	/* 将pIndx 进行分组 */
	uInt32 groupNums = wCnt / 256; // 一组256 个数字
	//groupNums += (wCnt % 256 == 0) ? 0 : 1; /* 计算分组个数 */
	groupNums += (GET_MOD(wCnt, 256) == 0) ? 0 : 1; /* 计算分组个数 */
	cout << "groupNums= " << groupNums << endl;
	/* 对cmpOutList 数组每个元素的idx 计算在pIndx的第几组，及0到255的哪个位置 */
	uInt32 *pGroupCnt = new uInt32[groupNums](); //统计每个组出现的频率，用于建立huffman树
	ASSERT_RELEASE((void*)pGroupCnt, pCharWeight, NULL);
	uInt32 *pInWhichGroup = new uInt32[cmpOutListNum](); //每个idx 在pIndex数组的第几个分组
	ASSERT_RELEASE((void*)pInWhichGroup, pCharWeight, pGroupCnt, NULL);
	uInt8 *pInGroupPos = new uInt8[cmpOutListNum](); // 每个idx在该分组内的什么位置
	ASSERT_RELEASE((void*)pInGroupPos, pInWhichGroup, pCharWeight, pGroupCnt, NULL);
	map<uInt32, uInt32>::iterator it;
	for(j = 0; j < cmpOutListNum; j++){
		it = mapIdx.find(pAllCmpListIdx[j]); //在mapIdx中查找
		if(it != mapIdx.end()){
			uInt32 whichGroup = it->second / 256;
			//uInt8 inGroupPos = (uInt8)((it->second % 256) & 0xff);
			uInt8 inGroupPos = (uInt8)(GET_MOD(it->second,256) & 0xff);
			my_printf("inGroupPos=%x, it->second=%x\n",inGroupPos, it->second);
			pGroupCnt[whichGroup]++;
			pInWhichGroup[j] = whichGroup;
			pInGroupPos[j] = inGroupPos;
		}
		else{
			cout << "(5) map idx to pIndx Fatail error!!!!!!!" << endl;
			break;
		}
	}

	delete [] pAllCmpListIdx;
	pAllCmpListIdx = NULL;
	/* (6) 用统计的分组出现频率做权重建立huffman树 */
	cout << "(6) start create group huffman tree:" << endl;
	stHuffmanTreeNode *pGroupHuffmanTree = NULL;
	uInt32 realLeafNum = 0;

	if(groupNums > 1){
		pGroupHuffmanTree = create_huffman_tree(pGroupCnt, groupNums, &realLeafNum);
		printf("groupNums = %d, realLeafNum = %d\n", groupNums, realLeafNum); 

		my_printf("pGroupHuffmanTree as follow:\n");
		for(j = 0; j < groupNums*2-1; j++){
			my_printf("[w, p, l, r]=%d:[%d, %d, %d, %d]\n",j,pGroupHuffmanTree[j].weight, \
				pGroupHuffmanTree[j].parent, pGroupHuffmanTree[j].leftChild, pGroupHuffmanTree[j].rightChild);
		}
		/* pGroupHuffmanTree树简化并保存 */
		stHuffmanTreeNodeSimple *pGroupHuffmanTreeSimple = new stHuffmanTreeNodeSimple[groupNums-1]();
		ASSERT_RELEASE((void*)pGroupHuffmanTreeSimple, pGroupHuffmanTree, pInGroupPos, pInWhichGroup, pCharWeight, pGroupCnt, NULL);
		for(j = 0; j < groupNums - 1; j++){
			pGroupHuffmanTreeSimple[j].leftChild = pGroupHuffmanTree[j + groupNums].leftChild;
			pGroupHuffmanTreeSimple[j].rightChild = pGroupHuffmanTree[j + groupNums].rightChild;
		}

		//fwrite(&groupNums, sizeof(uInt32), 1, pFout);
		memcpy(pOutData, &groupNums, sizeof(uInt32));
		pOutData += sizeof(uInt32);
		compressTotalBytes += sizeof(uInt32);
		//fwrite(pGroupHuffmanTreeSimple, (groupNums-1)*sizeof(stHuffmanTreeNodeSimple), 1, pFout);
		memcpy(pOutData, pGroupHuffmanTreeSimple, (groupNums-1)*sizeof(stHuffmanTreeNodeSimple));
		pOutData += (groupNums-1)*sizeof(stHuffmanTreeNodeSimple);
		compressTotalBytes += (groupNums-1)*sizeof(stHuffmanTreeNodeSimple);
		
		my_dump_data("./pGroupHuffmanTreeSimple_1.data", pGroupHuffmanTreeSimple, (groupNums-1)*sizeof(stHuffmanTreeNodeSimple));
		my_dump_data("./pInWhichGroup_1.data", pInWhichGroup, cmpOutListNum*sizeof(uInt32));

		delete [] pGroupHuffmanTreeSimple;
		pGroupHuffmanTreeSimple = NULL;
	}
	else{
		if(groupNums == 1){
			//fwrite(&groupNums, sizeof(uInt32), 1, pFout);
			memcpy(pOutData, &groupNums, sizeof(uInt32));
			pOutData += sizeof(uInt32);
			compressTotalBytes += sizeof(uInt32);
		}
	}

	delete [] pGroupCnt;
	pGroupCnt = NULL;
	
	cout << "=======pGroupHuffmanTreeSimple total bytes = " << (groupNums-1)*sizeof(stHuffmanTreeNodeSimple) << endl;
	
	/* (7) 对每个idx 在哪个组pInWhichGroup[] 进行huffman编码 */
	cout << "(7) start huffman encode pInWhichGroup[]:" << endl;
	if(pGroupHuffmanTree && groupNums > 1){
		vector<uInt32> whichGroupHuffmanCode;
		huffman_encode_idxGroup(pInWhichGroup, cmpOutListNum, pGroupHuffmanTree, groupNums, whichGroupHuffmanCode);
		uInt32 *pWhichGroupHuffmanCode = new uInt32[whichGroupHuffmanCode.size()]();
		ASSERT_RELEASE((void*)pWhichGroupHuffmanCode, pGroupHuffmanTree, pInGroupPos, pInWhichGroup, pCharWeight, NULL);
		for(j = 0; j < whichGroupHuffmanCode.size(); j++){
			pWhichGroupHuffmanCode[j] = whichGroupHuffmanCode[j];
		}

		//fwrite(&cmpOutListNum, sizeof(uInt32), 1, pFout);
		memcpy(pOutData, &cmpOutListNum, sizeof(uInt32));
		pOutData += sizeof(uInt32);
		compressTotalBytes += sizeof(uInt32);
		//fwrite(&j, sizeof(uInt32), 1, pFout);
		memcpy(pOutData, &j, sizeof(uInt32));
		pOutData += sizeof(uInt32);
		compressTotalBytes += sizeof(uInt32);
		//fwrite(pWhichGroupHuffmanCode, j * sizeof(uInt32), 1, pFout);
		memcpy(pOutData, pWhichGroupHuffmanCode, j * sizeof(uInt32));
		pOutData += j * sizeof(uInt32);
		compressTotalBytes += j * sizeof(uInt32);

		my_dump_data("./pWhichGroupHuffmanCode_1.data", pWhichGroupHuffmanCode, j * sizeof(uInt32));

		delete [] pWhichGroupHuffmanCode;
		pWhichGroupHuffmanCode = NULL;
		cout << "=======whichGroupHuffmanCode bytes = " << j * sizeof(uInt32) << endl;
	}
	else{
		//fwrite(&cmpOutListNum, sizeof(uInt32), 1, pFout);
		memcpy(pOutData, &cmpOutListNum, sizeof(uInt32));
		pOutData += sizeof(uInt32);
		compressTotalBytes += sizeof(uInt32);
		cout << "=======whichGroupHuffmanCode bytes = " << 0 << endl;
	}
	
	delete [] pInWhichGroup;
	pInWhichGroup = NULL;
	delete [] pGroupHuffmanTree;
	pGroupHuffmanTree = NULL;
	
	/* (8) 写入每个idx 在各自的组中的位置信息pInGroupPos */
	cout << "(8) start write pInGroupPos[] to file:" << endl;
	//fwrite(pInGroupPos, cmpOutListNum * sizeof(uInt8), 1, pFout);
	memcpy(pOutData, pInGroupPos, cmpOutListNum * sizeof(uInt8));
	pOutData += cmpOutListNum * sizeof(uInt8);
	compressTotalBytes += cmpOutListNum * sizeof(uInt8);
	cout << "=======pInGroupPos bytes = " << cmpOutListNum << endl;

	my_dump_data("./pInGroupPos_1.data", pInGroupPos, cmpOutListNum*sizeof(uInt8));

	/* (9) 为c 元素建立huffman树 */
	cout << "(9) start create pCharHuffmanTree:" << endl;
	stHuffmanTreeNode *pCharHuffmanTree = NULL;
	pCharHuffmanTree = create_huffman_tree(pCharWeight, 256, &realLeafNum);
	printf("pCharHuffmanTree realLeafNum = %d\n", realLeafNum); 
	for(j = 0; j < 256; j++){
		my_printf("pCharWeight[%d]: %d", j, pCharWeight[j]);
	}
	
	delete [] pInGroupPos;
	pInGroupPos = NULL;

	my_printf("pCharHuffmanTree as follow:\n");
	for(j = 0; j < 256*2-1; j++){
		if(pCharHuffmanTree[j].weight == 0 && pCharHuffmanTree[j].parent == 0 &&
			pCharHuffmanTree[j].leftChild == 0 && pCharHuffmanTree[j].rightChild == 0){
			continue;
		}
		my_printf("[w, p, l, r]=%d:[%d, %d, %d, %d]\n",j,pCharHuffmanTree[j].weight, \
			pCharHuffmanTree[j].parent, pCharHuffmanTree[j].leftChild, pCharHuffmanTree[j].rightChild);
	}

	/* (10) pCharHuffmanTree树简化并保存 */
	cout << "(10) start simpfy pCharHuffmanTree and save:" << endl;
	uInt8 charSimpleHuffmanTreeSize = 0;
	if(realLeafNum > 1){
		charSimpleHuffmanTreeSize = (realLeafNum - 1) & 0xff;
	}
	else{
		charSimpleHuffmanTreeSize = 0;
	}
	printf("charSimpleHuffmanTreeSize = %d\n", charSimpleHuffmanTreeSize);
	stHuffmanTreeNodeCharSimple *pCharHuffmanTreeSimple = new stHuffmanTreeNodeCharSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimple, NULL);

	uInt8 bitMapNum = (charSimpleHuffmanTreeSize*2) / 8; //左右节点的index都需要映射
	//bitMapNum = ((charSimpleHuffmanTreeSize*2) % 8 == 0) ? bitMapNum : (bitMapNum+1);
	bitMapNum = (GET_MOD(charSimpleHuffmanTreeSize*2, 8) == 0) ? bitMapNum : (bitMapNum+1);
	uInt8 pCharHuffmanTreeBitMap[64] = {0}; 

	uInt16 bitPos = 0;
	for(j = 0; j < charSimpleHuffmanTreeSize; j++){
		uInt32 leftChildIdx = pCharHuffmanTree[j + 256+(256-realLeafNum)].leftChild;
		uInt32 rightChildIdx = pCharHuffmanTree[j + 256+(256-realLeafNum)].rightChild;
		if(leftChildIdx >= 256){
			setBit_uInt8(pCharHuffmanTreeBitMap, bitPos++); //如果大于叶子节点的个数则需要映射
			pCharHuffmanTreeSimple[j].leftChild = (leftChildIdx - 256) & 0xff;
		}
		else{
			pCharHuffmanTreeSimple[j].leftChild = leftChildIdx & 0xff;
			bitPos++;
		}

		if(rightChildIdx >= 256){
			setBit_uInt8(pCharHuffmanTreeBitMap, bitPos++); //如果大于叶子节点的个数则需要映射
			pCharHuffmanTreeSimple[j].rightChild = (rightChildIdx - 256)  & 0xff;
		}
		else{
			pCharHuffmanTreeSimple[j].rightChild = rightChildIdx & 0xff;
			bitPos++;
		}
	}

	//fwrite(&charSimpleHuffmanTreeSize, sizeof(uInt8), 1, pFout); //这个值不会超过256所以一个字节就可以了
	memcpy(pOutData, &charSimpleHuffmanTreeSize, sizeof(uInt8));
	pOutData += sizeof(uInt8);
	compressTotalBytes += sizeof(uInt8);
	//fwrite(pCharHuffmanTreeBitMap, sizeof(uInt8) * bitMapNum, 1, pFout); //写入映射表
	memcpy(pOutData, pCharHuffmanTreeBitMap, sizeof(uInt8) * bitMapNum);
	pOutData += sizeof(uInt8) * bitMapNum;
	compressTotalBytes += sizeof(uInt8) * bitMapNum;
	cout << "=======pCharHuffmanTreeSimple BitMap total bytes = " << sizeof(uInt8) * bitMapNum << endl;
	//fwrite(pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple), 1, pFout);
	memcpy(pOutData, pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	pOutData += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);
	compressTotalBytes += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);

	my_dump_data("./pCharHuffmanTreeSimple1.data", pCharHuffmanTreeSimple, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	
	delete [] pCharHuffmanTreeSimple;
	pCharHuffmanTreeSimple = NULL;
	cout << "=======pCharHuffmanTreeSimple Tree total bytes = " << charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple) << endl;

	/* (11) 对char 进行huffman 编码 */
	cout << "(11) start huffman encode for char:" << endl;
	vector<uInt32> charHuffmanCode;
	huffman_encode_char(pAllCmpListChar, cmpOutListNum, pCharHuffmanTree, 256, charHuffmanCode);

	delete [] pAllCmpListChar;
	pAllCmpListChar = NULL;
	
	uInt32 *pCharHuffmanCode = new uInt32[charHuffmanCode.size()]();
	ASSERT_RELEASE((void*)pCharHuffmanCode, NULL);
	for(j = 0; j < charHuffmanCode.size(); j++){
		pCharHuffmanCode[j] = charHuffmanCode[j];
	}
	//fwrite(&j, sizeof(uInt32), 1, pFout);
	memcpy(pOutData, &j, sizeof(uInt32));
	pOutData += sizeof(uInt32);
	compressTotalBytes += sizeof(uInt32);
	//fwrite(pCharHuffmanCode, j * sizeof(uInt32), 1, pFout);
	memcpy(pOutData, pCharHuffmanCode, sizeof(uInt32) * j);
	pOutData += sizeof(uInt32) * j;
	compressTotalBytes += j * sizeof(uInt32);

	delete [] pCharHuffmanCode;
	pCharHuffmanCode = NULL;
	delete [] pCharHuffmanTree;
	pCharHuffmanTree = NULL;
	cout << "=======pCharHuffmanCode bytes = " << j * sizeof(uInt32) << endl;

	printf("After lz78 compress total bytes=%d, compress rate: %.2f%%\n",
		compressTotalBytes, (double)compressTotalBytes / totalBytes * 100);
	return compressTotalBytes;
}

uInt32 my_decompress_file_lz78(void *pData, uInt32 totalBytes, FILE* pFout)
{
	if(!pData || !pFout)
		return 0;
	my_printf("It is use lz78 algorithm to decompress!\n");

	uInt8 *pInData = (uInt8*)pData;
	uInt32 wCnt = *((uInt32*)pInData);
	pInData += sizeof(uInt32);

	/* (1) pIndex数组从bitMap中解压出来 */
	cout << "(1) wCnt = " << wCnt << endl;
	uInt32 *pIndex = new uInt32[wCnt]();
	CHECK_POINTER_NULL(pIndex, 0);
	uInt32 i = 0;
	uInt32 index = 0;
	while(i < wCnt){
		if(tstBit_uInt8(pInData, index)){
			//cout << index << endl;
			pIndex[i++] = index;
		}
		index++;
	}

	uInt32 idxBitMapNums = pIndex[wCnt-1] / 8; 
	idxBitMapNums++;
	printf("(2) max index = %d, need %d uInt8 to save\n", pIndex[wCnt-1], idxBitMapNums);
	my_dump_data("./pIdxBitMap_2.data", pInData, idxBitMapNums * sizeof(uInt8));

	pInData += (idxBitMapNums * sizeof(uInt8));
	my_dump_data("./pIndex_2.data", pIndex, sizeof(uInt32)*wCnt);

	/*(2) pGroupHuffmanTree的获取*/
	uInt32 groupNum = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	cout << "(3) groupNum = " << groupNum << endl;

	uInt32 cmpOutListNum = 0;
	uInt32 *pInWhichGroup = NULL;
	if(groupNum > 1){
		stHuffmanTreeNodeSimple *pGroupHuffmanTreeSimple = new stHuffmanTreeNodeSimple[groupNum-1]();
		ASSERT_RELEASE((void*)pGroupHuffmanTreeSimple, pIndex, NULL);
		memcpy(pGroupHuffmanTreeSimple, pInData, (groupNum-1)*sizeof(stHuffmanTreeNodeSimple));
		pInData += ((groupNum-1)*sizeof(stHuffmanTreeNodeSimple));

		my_dump_data("./pGroupHuffmanTreeSimple_2.data", pGroupHuffmanTreeSimple, (groupNum-1)*sizeof(stHuffmanTreeNodeSimple));

		cmpOutListNum = *((uInt32*)pInData);
		pInData += sizeof(uInt32);

		uInt32 inWhichGroupHuffmanCodeNum = *((uInt32*)pInData);
		pInData += sizeof(uInt32);
		printf("(4)cmpOutListNum=%d, inWhichGroupHuffmanCodeBytes = %d\n)",
			cmpOutListNum, inWhichGroupHuffmanCodeNum*sizeof(uInt32));

		/* 从文件中获取inWhichGroup 的huffman编码 */
		vector<uInt32> whichGroupHuffmanCode;
		for(i = 0; i < inWhichGroupHuffmanCodeNum; i++){
			uInt32 codeValue = *((uInt32*)pInData);
			//printf("codeValue = %x\n", codeValue);
			whichGroupHuffmanCode.push_back(codeValue);
			pInData += sizeof(uInt32);
		}

		#if NEED_DUMP_DATA
		uInt32 *pWhichGroupHuffmanCode = new uInt32[inWhichGroupHuffmanCodeNum]();
		ASSERT_RELEASE((void*)pWhichGroupHuffmanCode, pIndex, pGroupHuffmanTreeSimple, NULL);
		for(i = 0; i < inWhichGroupHuffmanCodeNum; i++){
			pWhichGroupHuffmanCode[i] = whichGroupHuffmanCode[i];
		}
		
		my_dump_data("./pWhichGroupHuffmanCode_2.data", pWhichGroupHuffmanCode, i * sizeof(uInt32));
		delete [] pWhichGroupHuffmanCode;
		pWhichGroupHuffmanCode = NULL;
		#endif

		pInWhichGroup = new uInt32[cmpOutListNum]();
		ASSERT_RELEASE((void*)pInWhichGroup, pIndex, pGroupHuffmanTreeSimple, NULL);
		huffman_decode_idxGroup(pGroupHuffmanTreeSimple, 
								whichGroupHuffmanCode,
								pInWhichGroup,
								cmpOutListNum,
								groupNum);	

		my_dump_data("./pInWhichGroup_2.data", pInWhichGroup, cmpOutListNum*sizeof(uInt32));

		delete [] pGroupHuffmanTreeSimple;
		pGroupHuffmanTreeSimple = NULL;
	}
	else{
		cmpOutListNum = *((uInt32*)pInData);
		pInData += sizeof(uInt32);
		printf("(4)cmpOutListNum=%d\n)", cmpOutListNum);
	}

	/* (3) 将idx 在各自组的什么位置提取出来 */
	uInt8 *pInGroupPos = new uInt8[cmpOutListNum]();
	ASSERT_RELEASE((void*)pInGroupPos, pIndex, pInWhichGroup, NULL);
	for(i = 0; i < cmpOutListNum; i++){
		pInGroupPos[i] = (uInt8)(pInData[i] & 0xff);
	}
	pInData += sizeof(uInt8) * cmpOutListNum;

	my_dump_data("./pInGroupPos_2.data", pInGroupPos, cmpOutListNum*sizeof(uInt8));

	/* (4) 还原lz78压缩出来的cmpList的所以idx值 */
	uInt32 *pAllCmpListIdx = new uInt32[cmpOutListNum]();
	ASSERT_RELEASE((void*)pAllCmpListIdx, pIndex, pInWhichGroup, pInGroupPos, NULL);
	for(i = 0; i < cmpOutListNum; i++){
		if(groupNum > 1){
			uInt32 pos = (uInt32)pInGroupPos[i] & 0xff;
			uInt32 pIndex_it = pInWhichGroup[i] * 256 + pos; //根据组号和组内序号获得pIndex的数组下标
			pAllCmpListIdx[i] =  pIndex[pIndex_it]; //获得对应下标的idx值
		}
		else{
			uInt32 pIndex_it = (uInt32)pInGroupPos[i] & 0xff;
			pAllCmpListIdx[i] = pIndex[pIndex_it];;
		}
	}

	my_dump_data("./pAllCmpListIdx_2.data", pAllCmpListIdx, cmpOutListNum*sizeof(uInt32));

	delete [] pInWhichGroup;
	pInWhichGroup = NULL;
	delete [] pInGroupPos;
	pInGroupPos = NULL;
	delete [] pIndex;
	pIndex = NULL;

	/* (5) 解压char 部分 */
	uInt8 charSimpleHuffmanTreeSize = (uInt8)*pInData;
	pInData++;
	printf("(5)charSimpleHuffmanTreeSize = %d\n" ,charSimpleHuffmanTreeSize);

	/* 获得char 的简单huffman树 */
	stHuffmanTreeNodeSimple *pCharHuffmanTreeSimple = new stHuffmanTreeNodeSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimple, pAllCmpListIdx, NULL);
	stHuffmanTreeNodeCharSimple *pCharHuffmanTreeSimpleTmp = new stHuffmanTreeNodeCharSimple[charSimpleHuffmanTreeSize]();
	ASSERT_RELEASE((void*)pCharHuffmanTreeSimpleTmp, pCharHuffmanTreeSimple, pAllCmpListIdx, NULL);

	uInt8 bitMapNum = (charSimpleHuffmanTreeSize*2) / 8; //左右节点的index都需要映射
	//bitMapNum = ((charSimpleHuffmanTreeSize*2) % 8 == 0) ? bitMapNum : (bitMapNum+1);
	bitMapNum = (GET_MOD(charSimpleHuffmanTreeSize*2, 8) == 0) ? bitMapNum : (bitMapNum+1);
	uInt8 pCharHuffmanTreeBitMap[64] = {0}; //最大64 = 256 * 2 /8

	memcpy(pCharHuffmanTreeBitMap, pInData, sizeof(uInt8) * bitMapNum); //获取映射表数据
	pInData += sizeof(uInt8) * bitMapNum;
	memcpy(pCharHuffmanTreeSimpleTmp, pInData, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));
	pInData += charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple);

	uInt16 bitPos = 0;
	for(i = 0; i < charSimpleHuffmanTreeSize; i++){
		enBool isMap = FALSE;
		isMap = tstBit_uInt8(pCharHuffmanTreeBitMap, bitPos++);
		if(isMap){
			pCharHuffmanTreeSimple[i].leftChild = pCharHuffmanTreeSimpleTmp[i].leftChild + 256;
		}
		else{
			pCharHuffmanTreeSimple[i].leftChild = pCharHuffmanTreeSimpleTmp[i].leftChild;
		}
		isMap = tstBit_uInt8(pCharHuffmanTreeBitMap, bitPos++);
		if(isMap){
			pCharHuffmanTreeSimple[i].rightChild = pCharHuffmanTreeSimpleTmp[i].rightChild + 256;
		}
		else{
			pCharHuffmanTreeSimple[i].rightChild = pCharHuffmanTreeSimpleTmp[i].rightChild;
		}
	}

	my_dump_data("./pCharHuffmanTreeSimple2.data", pCharHuffmanTreeSimpleTmp, charSimpleHuffmanTreeSize*sizeof(stHuffmanTreeNodeCharSimple));

	delete [] pCharHuffmanTreeSimpleTmp;
	pCharHuffmanTreeSimpleTmp = NULL;

	/* 获得char 的huffman编码uInt32 的个数 */
	uInt32 charHuffmanCodeNums = *((uInt32*)pInData);
	pInData += sizeof(uInt32);
	cout << "charHuffmanCodeBytes = " << charHuffmanCodeNums * sizeof(uInt32) << endl;

	vector<uInt32> charHuffmanCode;
	for(i = 0; i < charHuffmanCodeNums; i++){
		uInt32 codeValue = *((uInt32*)pInData);
		charHuffmanCode.push_back(codeValue);
		pInData += sizeof(uInt32);
	}

	uInt8 *pAllCmpListChar = new uInt8[cmpOutListNum]();
	ASSERT_RELEASE((void*)pAllCmpListChar, pAllCmpListIdx, pCharHuffmanTreeSimple, NULL);
	huffman_decode_char(pCharHuffmanTreeSimple, 
						charHuffmanCode,
						pAllCmpListChar,
						cmpOutListNum,
						256,
						charSimpleHuffmanTreeSize+1); //实际的叶子节点数比简单huffman数组个数多一个

	my_dump_data("./pCmpListChar_2.data", pAllCmpListChar, cmpOutListNum*sizeof(uInt8));

	delete [] pCharHuffmanTreeSimple;
	pCharHuffmanTreeSimple = NULL;

	/* (6) 将解压出来的idx 和c 还原到stLZ78CmpCp结构体中 */
	vector<stLZ78CmpCp> cmpOutList;
	for(i = 0; i < cmpOutListNum; i++){
		stLZ78CmpCp item;
		item.idx = pAllCmpListIdx[i];
		item.c = (uInt8)pAllCmpListChar[i] & 0xff;
		cmpOutList.push_back(item);
	}

	delete [] pAllCmpListIdx;
	pAllCmpListIdx = NULL;
	delete [] pAllCmpListChar;
	pAllCmpListChar = NULL;
	

	/* 解码lz78算法压缩的数据 */
	uInt32 decompressTotalBytes = 0;
	printf("cmpOutList.size() = %d\n", cmpOutList.size());
	uInt32 cmpBeforeBytes = (BLOCK_BYTES + 8) & (~(sizeof(uInt32) - 1));
	uInt8 *pDecmpOutData = new uInt8[cmpBeforeBytes]();
	CHECK_POINTER_NULL(pDecmpOutData, 0);
		
	decompressTotalBytes = my_LZ78_decompress(cmpOutList, pDecmpOutData);
	if(pDecmpOutData[decompressTotalBytes - 1] == '\0'){
		decompressTotalBytes--;
	}
	fwrite(pDecmpOutData, sizeof(uInt8)*decompressTotalBytes, 1, pFout);

	delete [] pDecmpOutData;
	pDecmpOutData = NULL;
	printf("Decompress total bytes = %d\n", decompressTotalBytes);
	return decompressTotalBytes;
}

void f1(int n){
	return;
}
void f2(int n){
	return;
}
void f3(int n){
	return;
}

void (*g_arry[])(int) = {
	f1, f2, f3
};

int main(int argc, char** argv)
{
	cout << sizeof(g_arry) / sizeof(g_arry[0]) << endl;

	uInt8 uca = 290, ucb = 390;
	uInt32 uia = 0xffffff00, uib = 0x2610;
	printf("%d, %d\n", ucb - uca, abs(uib - uia));
	
	Int32 next[100] = { 0 };
	Int8 mainStr[100] = {0};
	Int8 subStr[100] = {0};
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdabde");
	sprintf(subStr, "%s", "abcdabd");
	cout << KMP_Search((uInt8*)mainStr, 23, (uInt8*)subStr, 7, next) << endl; //15
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdabcd");
	cout << KMP_Search((uInt8*)mainStr, 23, (uInt8*)(mainStr+15), 8, next) << endl; //11
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdaacd");
	cout << KMP_Search((uInt8*)mainStr, 23, (uInt8*)(mainStr+15), 8, next) << endl; //15
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdaacd");
	cout << KMP_Search((uInt8*)mainStr, 22, (uInt8*)(mainStr+15), 8, next) << endl; //-1
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdaacd");
	cout << KMP_Search((uInt8*)mainStr, 23, (uInt8*)(mainStr+15), 4, next) << endl; // 4

	sprintf(mainStr, "%s", "bbc abcdab abcdabcdabde");
	sprintf(subStr, "%s", "abcdabd");
	cout << Sunday_Search((uInt8*)mainStr, 23, (uInt8*)subStr, 7) << endl; //15
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdabcd");
	cout << Sunday_Search((uInt8*)mainStr, 23, (uInt8*)(mainStr+15), 8) << endl; //11
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdaacd");
	cout << Sunday_Search((uInt8*)mainStr, 23, (uInt8*)(mainStr+15), 8) << endl; //15
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdaacd");
	cout << Sunday_Search((uInt8*)mainStr, 22, (uInt8*)(mainStr+15), 8) << endl; //-1
	sprintf(mainStr, "%s", "bbc abcdab abcdabcdaacd");
	cout << Sunday_Search((uInt8*)mainStr, 23, (uInt8*)(mainStr+15), 4) << endl; // 4
	#if 0
	mkdir("123", S_IRWXU | S_IRWXG | S_IRWXO);
	stDate date = {0};
	my_get_current_date(&date);
	//struct timespec ts;
	//clock_gettime(CLOCK_REALTIME, &ts);
	
	struct timeval tv;
    gettimeofday(&tv,NULL);
	printf("nowTime: [%04d/%02d/%02d, %02d:%02d:%02d.%03d]\n",
		date.year, date.mon, date.mday, date.hour,
		date.min, date.sec, tv.tv_usec/1000);

	char tmp[256] = {'\0'};
	int len = sprintf(tmp, "[%04d/%02d/%02d, %02d:%02d:%02d.%03d]\n",
		date.year, date.mon, date.mday, date.hour,
		date.min, date.sec, tv.tv_usec/1000);
	cout << "len = " << len << ";" << tmp << endl;
	
	vector<uInt32> in;
	vector<uInt32> out;
	uInt8 i = 0;
	for(; i < 10; i++){
		in.push_back(i * 17);
	}

	golomb_rice_encode(in, out);
	cout << "after golomb encode:" << endl;
	for(i = 0; i < out.size(); i++){
		printf("[%d] %x\n",i, out[i]);
	}

	in.clear();
	cout << "after golomb decode:" << endl;
	golomb_rice_decode(out, in, 10);
	for(i = 0; i < in.size(); i++){
		printf("[%d] %d\n",i, in[i]);
	}

	cout << "********* combine test ***********" << endl;
	uInt32 cmbSrc[4] = {0x123, 0x345, 0x567, 0x789};
	uInt8 cmbDst[7] = {0};
	combine_bits(cmbSrc, 4, 12, cmbDst);
	for(i = 0; i < 7; i++){
		printf("%x ", cmbDst[i]);
	}
	cout << endl;

	memset(cmbSrc, 0, sizeof(uInt32)*4);
	decombine_bits(cmbDst, 4, 12, cmbSrc);
	for(i = 0; i < 4; i++){
		printf("%x ", cmbSrc[i]);
	}
	cout << endl;
	cout << "********* combine test end***********" << endl;

	#if 1 //test huffman tree
	stWeightToIdx a, b;
	a.weight = 10;
	a.index = 100;
	b.weight = 12;
	b.index = 120;
	my_swap(a, b);
	my_printf("a=(%d,%d), b=(%d,%d)\n", a.weight,a.index,b.weight,b.index);

	stHuffmanTreeNode *pHuffmanTree = NULL;
	uInt32 weight[11] = {0, 5, 29, 7, 0 , 8, 14, 23, 3, 11, 0};
	//uInt32 weight[8] = { 5, 29, 7,  8, 14, 23, 3, 11};
	uInt32 n = 11;
	uInt32 realLeafNum = 0;
	pHuffmanTree = create_huffman_tree(weight, n, &realLeafNum);
	cout << "realLeafNum = " << realLeafNum << endl;
	for(i = 0; i < 2*n-1; i++){
		my_printf("[w, p, l, r]=%d:[%d, %d, %d, %d]\n",i,pHuffmanTree[i].weight, \
			pHuffmanTree[i].parent, pHuffmanTree[i].leftChild, pHuffmanTree[i].rightChild);
	}

	vector<uInt32> outCode;
	huffman_encode(pHuffmanTree, n, outCode);

	for(i = 0; i < outCode.size(); i++){
		my_printf("%x\n", outCode[i]);
	}

	memset(weight, 0, sizeof(uInt32) * n);
	huffman_decode(pHuffmanTree, outCode, weight, n);
	for(i = 0; i < realLeafNum; i++){
		my_printf("%d ", weight[i]);
	}
	cout << endl;

	stHuffmanTreeNodeSimple huffmanTreeSimple[n-1];
	for(i = 0; i < realLeafNum-1; i++){
		huffmanTreeSimple[i].leftChild = pHuffmanTree[i + n+(n-realLeafNum)].leftChild;
		huffmanTreeSimple[i].rightChild = pHuffmanTree[i + n+(n-realLeafNum)].rightChild;
		my_printf("huffmanTreeSimple[%d] : left = %d, right=%d\n",i, huffmanTreeSimple[i].leftChild, huffmanTreeSimple[i].rightChild);
	}

	uInt32 index[11] = {0};
	huffman_decode_simple(huffmanTreeSimple, outCode, index, n, realLeafNum);
	for(i = 0; i < n; i++){
		cout << index[i] << " ";
	}
	cout << endl;
	
	delete [] pHuffmanTree;
	pHuffmanTree = NULL;
	#endif


	//uInt32 sum = 0;
	//for(i = 0; i < 500; i++){
	//	sum += i;
	//}
	//cout << "sum = " << sum << endl;

	uInt32 test[2] = {0x12345678, 0x9abcdef0};
	void *pTest = (void*)test;
	uInt8 *pTestC = (uInt8*)pTest;
	for(i = 0; i < 8; i++){
		printf("%x ", pTestC[i]);
	}
	cout << endl;

	uInt8 bitMap_8bit[10] = {0};
	for(i = 0; i < 18; i++){
		setBit_uInt8(bitMap_8bit, i);
	}
	setBit_uInt8(bitMap_8bit, 79);

	for(i = 0; i < 10; i++){
		printf("%x ", bitMap_8bit[i]);
	}
	cout << endl;

	#if 0
	uInt32 *pa = new uInt32[10];
	stCmpFileHead *pb = new stCmpFileHead[3];
	stCmpFileHead *pc = NULL;

	ASSERT_RELEASE((void*)pc, 0, pa, pb, NULL);

	//delete [] v[0];
	//delete [] v[1];

	delete [] pa;
	delete [] pb;
	#endif
	
    #if 0 //test MAP
	map<uInt32, stDictionaryItem> dictionaryMap;
	stDictionaryItem it1;
	it1.idx = 100;
	dictionaryMap[100] = it1;
	map<uInt32, stDictionaryItem>::iterator it;
	it = dictionaryMap.find(101);
	if(it != dictionaryMap.end()){
		my_printf("Find, idx=%d\n", it->second.idx);
	}
	else{
		my_printf("Can not find!\n");
	}

	map<uInt32, uInt32> testMap;
	testMap[10] = 19;
	if(testMap[11] != 0){
		my_printf("Find, idx=%d\n", testMap[10]);
	}
	else{
		my_printf("Can not find! testMap[11]=%d\n", testMap[11]);
	}

	map<uInt32, vector<stDictionaryItem> > dictionaryMap2;
	map<uInt32, vector<stDictionaryItem> >::iterator it2;
	if((it2 = dictionaryMap2.find(100)) == dictionaryMap2.end()){
		vector<stDictionaryItem> itemList;
		stDictionaryItem item;
		item.len = 100;
		itemList.push_back(item);
		dictionaryMap2.insert(make_pair(100, itemList));
	}

	if((it2 = dictionaryMap2.find(100)) != dictionaryMap2.end()){
		stDictionaryItem item;
		item.len = 101;
		it2->second.push_back(item);
	}

	int i = 0;
	for(; i < it2->second.size(); i++){
		my_printf("&&& %d\n", it2->second[i].len);
	}
	#endif
	
	#if 0 /* Test */
	uInt8 *cmpStr = "aacaacabcabaaacbaaacccaacabcad";
	//char *cmpStr = "abcdefabcjklmnaacaacabcabaaac";
	vector<stLZ77CmpCp> cmpArry;
	my_LZ77_compress(cmpStr, 30, &cmpArry);
	cout << "sizeof(cmpArry) = " << sizeof(cmpArry) << endl;
	char out[30] = {'\0'};
	uInt32 len = my_LZ77_decompress(cmpArry, out);
	cout << "src:" << cmpStr << endl;
	cout << "dst:" << out << "; len = 0x" << len << endl;

	vector<stLZ78CmpCp> cmpArry_Lz78;

	my_LZ78_compress(cmpStr, 30, &cmpArry_Lz78);
	for(len = 0; len < cmpArry_Lz78.size(); len++){
		my_printf("[%d](%d, %c)\n", len+1, cmpArry_Lz78[len].idx, cmpArry_Lz78[len].c);
	}
	memset(out, '\0', 30);
	len = my_LZ78_decompress(cmpArry_Lz78, out);
	cout << "src:" << cmpStr << endl;
	cout << "dst:" << out << "; len = 0x" << len << endl;
	
	cmpArry_Lz78.clear();
	char *cmpStr_lz78 = "ABBCBCABABCAABCAAB";
	my_LZ78_compress(cmpStr_lz78, 18, &cmpArry_Lz78);
	//char *cmpStr_lz78 = "BABAABRRRA";
	//my_LZ78_compress(cmpStr_lz78, 10, &cmpArry_Lz78);
	for(len = 0; len < cmpArry_Lz78.size(); len++){
		my_printf("[%d](%d, %c)\n", len+1, cmpArry_Lz78[len].idx, cmpArry_Lz78[len].c);
	}

	memset(out, '\0', 30);
	len = my_LZ78_decompress(cmpArry_Lz78, out);
	cout << "src:" << cmpStr_lz78 << endl;
	cout << "dst:" << out << "; len = 0x" << len << endl;
	#endif
	#endif

	if(argc != 3 && argc != 4 && argc != 5 && argc != 7){
        my_error("invalide args, usage:./my_compress -i[or --file_in] <input file name> [-o[or --file_out] <output file name>] " \
			"[-c (or --compress)] <lz77/lz78>");
        return - 1;
    }
    
    char *short_options = "i:o:c:"; 
    static struct option long_options[] = {  
       //{"reqarg", required_argument, NULL, 'r'},  
       //{"noarg",  no_argument,       NULL, 'n'},  
       //{"optarg", optional_argument, NULL, 'o'}, 
       //{"device", required_argument, NULL, 'd'+'l'},
       {"file_in", required_argument, NULL, 'i'+'l'},
       {"file_out", optional_argument, NULL, 'o'+'l'},
	   {"compress", required_argument, NULL, 'c'+'l'},
       {0, 0, 0, 0}  
   };  

    int opt = 0;
    char file_in[128] = {'\0'};
	char file_out[128] = {'\0'};
	enBool bCompress = FALSE, bUseLz77 = FALSE;
    while((opt = getopt_long(argc, argv, short_options, long_options, NULL)) != -1){
        //my_printf("opt = %d, c=%d\n", opt, 'c');
        switch(opt){
            case 'i':
            case 'i'+'l':
                if(optarg){
					cout << "file_in name: " << optarg << endl;
					strncpy(file_in, optarg, strlen(optarg));
                }
                else
                    cout << "file_in name optarg is null" << endl;
                break;
            case 'o':
            case 'o'+'l':
                if(optarg){
                    cout << "file_out name: " << optarg << endl;
					strncpy(file_out, optarg, strlen(optarg));
                }
                else
                    cout << "file_out name optarg is null" << endl;
                break;
	     	case 'c':
            case 'c'+'l':
		   		//cout << "aaa" << optarg << endl;
                if(optarg){
                    cout << "compress: " << optarg << endl;
					if(strncmp(optarg, "lz77", 4) == 0){
						bUseLz77 = TRUE;
					}
					bCompress = TRUE; //压缩操作
                }
                break;
            default:
                break;
        }
    }

	if(file_out[0] == '\0'){
		strcpy(file_out, "./out");
	}

	cout << "file_in:" << file_in << "; "<< "file_out:" << file_out << endl;

	FILE *pFin = fopen(file_in, "rb");
	if(pFin == NULL){
		cout << "open: " << file_in << " Fail!!" << endl;
		return -1;
	}
	
	FILE *pFout = fopen(file_out, "wb");
	if(pFout == NULL){
		cout << "open: " << file_out << " Fail!!" << endl;
		return -1;
	}

	#if NEED_DUMP_DATA
	FILE *pFd = NULL;
	#endif
	
	uInt8 *pData = new uInt8[BLOCK_BYTES << 1](); //添加() 会初始化内存的数据
	uInt32 getDataBytes = 0, totalCmpBytes = 0, totalDecmpBytes = 0;
	Int32 ms_total = 0;
	ms_total = my_calc_process_time(NULL);
	if(bCompress){ /* compress file */
		if(bUseLz77){
			fileHeadInfo.cmp_head_code[3] = '7';
		}
		else{
			fileHeadInfo.cmp_head_code[3] = '8';
		}
		fileHeadInfo.cmp_before_bytes = 0;
		fileHeadInfo.block_num = 0;
		fwrite(&fileHeadInfo, sizeof(stCmpFileHead), 1, pFout);

		uInt8 *pBlockCmpData = new uInt8[BLOCK_BYTES << 1](); //由于压缩后的数据不一定不block小
		printf("#################################################\n");
		while((getDataBytes = read_file_content(pData, BLOCK_BYTES, pFin)) != 0){
			uInt8 *pInData = pData;	
			uInt32 blockCmpBytes = 0;
			fileHeadInfo.block_num++;
			fileHeadInfo.cmp_before_bytes += getDataBytes;
	        printf("Get block[%d] total src file bytes = %d\n", fileHeadInfo.block_num, getDataBytes);
			if(bUseLz77){ /* use lz77 algorithm to compress file */
				Int32 ms = 0;
				ms = my_calc_process_time(NULL);
				blockCmpBytes = my_compress_file_lz77(pInData, getDataBytes, pBlockCmpData);
				ms = my_calc_process_time(&ms);
				printf("[***TIME***] block[%d] cmpress spend %d ms!!!\n", fileHeadInfo.block_num, ms);
			}
			else{
				Int32 ms = 0;
				ms = my_calc_process_time(NULL);
				blockCmpBytes = my_compress_file_lz78(pInData, getDataBytes, pBlockCmpData);
				ms = my_calc_process_time(&ms);
				printf("[***TIME***] block[%d] cmpress spend %d ms!!!\n", fileHeadInfo.block_num, ms);
			}
		
			totalCmpBytes += sizeof(uInt32);
			fwrite(&blockCmpBytes, sizeof(uInt32), 1, pFout);
			totalCmpBytes += blockCmpBytes;
			fwrite(pBlockCmpData, blockCmpBytes * sizeof(uInt8), 1, pFout);

			my_dump_data("./BlockCmp_1.data",pBlockCmpData,blockCmpBytes * sizeof(uInt8));
			
			memset(pData, 0, sizeof(uInt8) * BLOCK_BYTES * 2);
			memset(pBlockCmpData, 0, sizeof(uInt8) * BLOCK_BYTES  *2);
			getDataBytes = 0;
			printf("#################################################\n");
		}

		delete [] pBlockCmpData;
		pBlockCmpData = NULL;

		/* 返回文件头重新写入文件头信息 */
		fseek(pFout, 0, SEEK_SET);
		fwrite(&fileHeadInfo, sizeof(stCmpFileHead), 1, pFout);

		printf("\033[1;33;42m<Final>: %s totalBytes = %d, compress total bytes=%d, compress rate: %.2f%%\033[0m\n", 
			bUseLz77 ? "LZ77" : "LZ78", fileHeadInfo.cmp_before_bytes,
			totalCmpBytes, (double)totalCmpBytes / fileHeadInfo.cmp_before_bytes * 100);
		ms_total = my_calc_process_time(&ms_total);
		printf("\033[1;33;42m[***TIME***]  All block compress spend %d ms!!!\033[0m\n", ms_total);
	}
	else{
		/* 读取头文件信息 */
		if(getDataBytes = read_file_content(pData, sizeof(stCmpFileHead), pFin) <= 0){
			my_error("Read file head infomation error!!!");
			delete [] pData;
			pData = NULL;
			return -1;	
		}
		memcpy(&fileHeadInfo, pData, sizeof(stCmpFileHead));
		Int8 myCode[3] = {'F','C','X'};
		if(memcmp(fileHeadInfo.cmp_head_code, myCode, 3) != 0){
			my_error("This file is not support to decompress!!!!");
			delete [] pData;
			pData = NULL;
			return -1;
		}

		if(fileHeadInfo.cmp_head_code[3] == '7'){
			bUseLz77 = TRUE;
		}else{
			bUseLz77 = FALSE;
		}

		printf("#################################################\n");
		uInt16 blockIdx = 0;
		for(; blockIdx < fileHeadInfo.block_num; blockIdx++){
			uInt32 blockBytes = 0;
			if((getDataBytes = read_file_content(&blockBytes, sizeof(uInt32), pFin)) <= 0){
				delete [] pData;
				pData = NULL;
				return -1;
			}
			printf("block [%d] block compress bytes = %d\n",blockIdx+1, blockBytes);
			if((getDataBytes = read_file_content(pData, blockBytes, pFin)) <= 0){
				delete [] pData;
				pData = NULL;
				return -1;
			}

			my_dump_data("./BlockCmp_2.data",pData,blockBytes * sizeof(uInt8));

			uInt8 *pBlockData = pData;
			if(bUseLz77){ // use lz77 algorithm
				Int32 ms = 0;
				ms = my_calc_process_time(NULL);
				totalDecmpBytes += my_decompress_file_lz77(pBlockData, getDataBytes, pFout);
				ms = my_calc_process_time(&ms);
				printf("[***TIME***] block[%d] decmpress spend %d ms!!!\n", blockIdx+1, ms);
			}
			else{
				Int32 ms = 0;
				ms = my_calc_process_time(NULL);
				totalDecmpBytes += my_decompress_file_lz78(pBlockData, getDataBytes, pFout);
				ms = my_calc_process_time(&ms);
				printf("[***TIME***] block[%d] decmpress spend %d ms!!!\n", blockIdx+1, ms);
			}
			printf("#################################################\n");
			
			memset(pData, 0, sizeof(uInt8) * BLOCK_BYTES * 2);
			getDataBytes = 0;
		}
		printf("All block decompress total bytes = %d, Compress Before bytes = %d [%s]\n", 
			totalDecmpBytes, fileHeadInfo.cmp_before_bytes, 
			(totalDecmpBytes == fileHeadInfo.cmp_before_bytes) ? 
			"\033[1;33;42mSUCCESS\033[0m" : "\033[1;31;43mFAIL\033[0m");
		ms_total = my_calc_process_time(&ms_total);
		printf("\033[1;33;42m[***TIME***]  All block decompress spend %d ms!!!\033[0m\n", ms_total);
	}
	

	delete [] pData;
	pData = NULL;

	//my_printf("sizeof(stLZ77CmpCp)=%d, sizeof(stLZ78CmpCp)=%d\n",
		//sizeof(stLZ77CmpCp), sizeof(stLZ78CmpCp));
	return 0;
}

