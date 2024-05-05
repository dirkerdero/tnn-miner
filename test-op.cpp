#include <algorithm>
#include <bit>
#include <bitset>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <random>

#include <arm_acle.h>
#include <arm_neon.h>
#include <climits>
#include <hugepages.h>

#include <arpa/inet.h>
#include <hex.h>

#include <openssl/rc4.h>
#include <openssl/sha.h>

#include <Salsa20.h>
#include <highwayhash/sip_hash.h>

extern "C"
{
  #include "divsufsort_private.h"
  #include "divsufsort.h"
}
#include <fnv1a.h>
#include <xxhash64.h>

using byte = unsigned char;

const unsigned char bitTable[256] = {
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 
    4, 3, 4, 4, 5, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 
    4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 
    3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 
    4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 1, 2, 2, 3, 2, 3, 3, 
    4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 
    3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 
    6, 6, 7, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 
    4, 5, 5, 6, 5, 6, 6, 7, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 4, 5, 5, 
    6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8
};

#define MAX_LENGTH 71000

class workerData
{
public:
  byte fixme[16];
  int bA[256];
  int bB[256*256];

  byte salsaInput[256] = {0};
  byte step_3[256];
  byte op;
  byte pos1;
  byte pos2;
  byte t1;
  byte t2;

  uint64_t lhash;
  uint64_t prev_lhash;
  uint64_t tries;
  uint64_t random_switcher;

  byte A;
  uint32_t data_len;

  byte *chunk;
  byte *prev_chunk;

  std::vector<byte> opsA;
  std::vector<byte> opsB;

  SHA256_CTX sha256;
  ucstk::Salsa20 salsa20;
  RC4_KEY key;

  byte sHash[32];

  byte sData[MAX_LENGTH+64];

  int32_t sa[MAX_LENGTH];
  bool opt[256] = {false};
};

uint8x16_t binary_not(uint8x16_t data) {
  //worker.chunk[i] = ~worker.chunk[i];
  // also maybe
  //const uint8x16_t ones = vdupq_n_u8(0xFF);
  // return vbicq_u8(data, ones);
  return vmvnq_u8(data);
}

uint8x16_t rotate_bits(uint8x16_t left_side, int rotation) {
  //worker.chunk[i] = std::rotl(worker.chunk[i], 3);
  //worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));
  rotation %= 8;
  return vorrq_u8(vshlq_n_u8(left_side, rotation), vshrq_n_u8(left_side, 8 - rotation));
}

uint8x16_t rotate_and_xor(uint8x16_t left_side, int rotation) {
  //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
  //rotation = rotation % 8;
  //rotation %= 8;
  //uint8x16_t rotated = vorrq_u8(vshlq_n_u8(left_side, rotation), vshrq_n_u8(left_side, 8 - rotation));

  // Perform XOR with original data
  return veorq_u8(left_side, rotate_bits(left_side, rotation));
}


uint8x16_t add_with_self(uint8x16_t a) {
  //worker.chunk[i] += worker.chunk[i];
  return vaddq_u8(a, a);
}

uint8x16_t mul_with_self(uint8x16_t a) {
  //worker.chunk[i] *= worker.chunk[i];
  return vmulq_u8(a, a);
}

uint8x16_t and_vectors(uint8x16_t a, uint8x16_t b) {
  //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
  // Perform XOR with original data
  return vandq_u8(a, b);
}

uint8x16_t xor_vectors(uint8x16_t a, uint8x16_t b) {
  //worker.chunk[i] ^= worker.chunk[worker.pos2];
  // Perform XOR with original data
  return veorq_u8(a, b);
}

uint8x16_t xor_with_bittable(uint8x16_t a) {
  //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
  auto count = vcntq_u8(a);
  // Perform XOR with original data
  return veorq_u8(a, count);
}


inline byte reverse_bits(byte byte) {
    static const uint8_t BitReverseTable256[256] = 
    {
        #define R2(n)     n,     n + 2*64,     n + 1*64,     n + 3*64
        #define R4(n) R2(n), R2(n + 2*16), R2(n + 1*16), R2(n + 3*16)
        #define R6(n) R4(n), R4(n + 2*4 ), R4(n + 1*4 ), R4(n + 3*4 )
        R6(0), R6(2), R6(1), R6(3)
    };
    
    return (BitReverseTable256[byte]);
}

inline uint8x16_t reverse_bits(uint8x16_t data) {
    return vrbitq_u8(data);
}

inline byte reverse8(byte b)
{
  return (b * 0x0202020202ULL & 0x010884422010ULL) % 1023;
}

uint8x16_t shift_left_by_int_with_and(uint8x16_t data, int andint) {
  //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
  // Note: This is signed!
  int8x16_t anded = vandq_s8(data, vdupq_n_u8(andint));
  return vshlq_u8(data, anded);
}

uint8x16_t shift_right_by_int_with_and(uint8x16_t data, int andint) {
  //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);
  // Note: This is signed!
  int8x16_t anded = vandq_s8(data, vdupq_n_u8(andint));

  // We can negate and left-shift to effectively do a right-shift;
  int8x16_t negated = vqnegq_s8(anded);
  return vshlq_u8(data, negated);
}

uint8x16_t subtract_xored(uint8x16_t data, int xor_value) {
  //worker.chunk[i] -= (worker.chunk[i] ^ 97);
  //auto xored = veorq_u8(data, vdupq_n_u8(xor_value));
  return vsubq_u8(data, veorq_u8(data, vdupq_n_u8(xor_value)));
}

uint8x16_t rotate_bits_by_vector(uint8x16_t data) {
  // see rotate_by_self
  //(worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
  // Shift left by the remainder of each element divided by 8
  uint8x16_t rotation_amounts = vandq_u8(data, vdupq_n_u8(7));

  //for(int x = 0; x < 16; x++) {
  //  printf("mod: %02x\n", rotation_amounts[x]);
  //}

  //uint8x16_t shifted_left = vshlq_u8(data, rotation_amounts);


  //uint8x16_t right_shift_amounts = vsubq_u8(vandq_u8(data, vdupq_n_u8(7)), vdupq_n_u8(8));
  //uint8x16_t right_shift_amounts = vsubq_u8(rotation_amounts, vdupq_n_u8(8));

  // Perform the right shift using left shift with negative amounts
  //return vshlq_u8(data, right_shift_amounts);
  // Shift right by (8 - remainder) of each element


  // Combine the shifted results using bitwise OR
  //return vorrq_u8(shifted_left, vshlq_u8(data, right_shift_amounts));
  return vorrq_u8(vshlq_u8(data, rotation_amounts), vshlq_u8(data, vsubq_u8(rotation_amounts, vdupq_n_u8(8))));
}

uint8x16_t rotate_by_self(uint8x16_t data) {
  //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
  //worker.chunk[i] = std::rotl(worker.chunk[i], worker.chunk[i]);
  return rotate_bits_by_vector(data);
}



// case 25
inline void oldschool(workerData &worker) {
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
          //uint8x16_t data = vld1q_u8(&worker.chunk[i]);
          worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
          //data = binary_not(data);
          
          //printf("c[i] >> (c[i] & 3) = %02x >> (%02x)\n", worker.chunk[i], (worker.chunk[i] & 3));
          //printf("c[i] >> (c[i] & 3) = %02x\n", (worker.chunk[i] & 3));
          worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
          //data = shift_right_by_int_with_and(data, 3);

          worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
          //data = rotate_by_self(data);

          worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
          //data = subtract_xored(data, 97);

          //vst1q_u8(&worker.chunk[i], data);
      }
}

// case 4:
inline void newschool(workerData &worker) {
        memcpy(worker.fixme, &worker.chunk[worker.pos2], (worker.pos2-worker.pos1)%16);
        //uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);
          //worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
          data = binary_not(data);
          
          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
          data = shift_right_by_int_with_and(data, 3);

          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
          data = rotate_by_self(data);

          //worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
          data = subtract_xored(data, 97);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, (worker.pos2-worker.pos1)%16);
}



bool debugOpOrder = false;
int sus_op = 25;

template <std::size_t N>
inline void generateInitVector(std::uint8_t (&iv_buff)[N])
{
  using random_bytes_engine = std::independent_bits_engine<std::default_random_engine,
                                                           CHAR_BIT, unsigned short>;
  random_bytes_engine rbe;

  std::generate(std::begin(iv_buff), std::end(iv_buff), rbe);
}

template <std::size_t N>
inline void generateRandomBytes(std::uint8_t (&iv_buff)[N])
{
  auto const hes = std::random_device{}();

  using random_bytes_engine = std::independent_bits_engine<std::default_random_engine,
                                                           CHAR_BIT, unsigned short>;

  random_bytes_engine rbe;
  rbe.seed(hes);

  std::generate(std::begin(iv_buff), std::end(iv_buff), std::ref(rbe));
}

inline bool littleEndian()
{
  int n = 1;
  // little endian if true
  if(*(char *)&n == 1) {
    return true;
  } 
  return false;
}



struct OpTestResult {
  unsigned char input[256];
  unsigned char result[256];
  std::chrono::nanoseconds duration_ns;
};


void branchComputeCPU_aarch64(workerData &worker, bool isTest)
{
  //if (debugOpOrder) printf("cpu\n");
  
  while (true)
  {
    if(isTest) {

    } else {
      worker.tries++;
      if (debugOpOrder) printf("t: 0x%lx p: 0x%lx l: 0x%lx\n", worker.tries, worker.prev_lhash, worker.lhash);
      worker.random_switcher = worker.prev_lhash ^ worker.lhash ^ worker.tries;
      // __builtin_prefetch(&worker.random_switcher,0,3);
      // printf("%d worker.random_switcher %d %08jx\n", worker.tries, worker.random_switcher, worker.random_switcher);

      worker.op = static_cast<byte>(worker.random_switcher);
      //if (debugOpOrder) worker.opsA.push_back(worker.op);

      // printf("op: %d\n", worker.op);

      worker.pos1 = static_cast<byte>(worker.random_switcher >> 8);
      worker.pos2 = static_cast<byte>(worker.random_switcher >> 16);

      if (worker.pos1 > worker.pos2)
      {
        std::swap(worker.pos1, worker.pos2);
      }

      if (worker.pos2 - worker.pos1 > 32)
      {
        worker.pos2 = worker.pos1 + ((worker.pos2 - worker.pos1) & 0x1f);
      }

      worker.chunk = &worker.sData[(worker.tries - 1) * 256];
      if (debugOpOrder) printf("worker.op: %03d p1: %03d p2: %03d\n", worker.op, worker.pos1, worker.pos2);

      if (worker.tries == 1) {
        worker.prev_chunk = worker.chunk;
      } else {
        worker.prev_chunk = &worker.sData[(worker.tries - 2) * 256];
        /*
        if (debugOpOrder) {
          printf("tries: %03lu prev_chunk[0->%03d]: ", worker.tries, worker.pos2);
          for (int x = 0; x <= worker.pos2+16 && worker.pos2+16 < 256; x++) {
            printf("%02x", worker.prev_chunk[x]);
          }
          printf("\n");
        }

        __builtin_prefetch(worker.prev_chunk,0,3);
        __builtin_prefetch(worker.prev_chunk+64,0,3);
        __builtin_prefetch(worker.prev_chunk+128,0,3);
        __builtin_prefetch(worker.prev_chunk+192,0,3);

        // Calculate the start and end blocks
        int start_block = 0;
        int end_block = worker.pos1 / 16;
        if (debugOpOrder) printf("loopa: %03lu %03d < %03d\n", worker.tries, start_block, end_block);

        // Copy the blocks before worker.pos1
        for (int i = start_block; i < end_block; i++) {
            __m128i prev_data = _mm_loadu_si128((__m128i*)&worker.prev_chunk[i * 16]);
            _mm_storeu_si128((__m128i*)&worker.chunk[i * 16], prev_data);
        }

        if (debugOpOrder) printf("loopb: %03lu %03d < %03d\n", worker.tries, end_block * 16, worker.pos1);
        // Copy the remaining bytes before worker.pos1
        for (int i = end_block * 16; i < worker.pos1; i++) {
            worker.chunk[i] = worker.prev_chunk[i];
        }

        // Calculate the start and end blocks
        start_block = (worker.pos2 + 15) / 16;
        end_block = 16;
        if (debugOpOrder) printf("loopc: %03lu %03d < %03d\n", worker.tries, start_block, end_block);

        // Copy the blocks after worker.pos2
        for (int i = start_block; i < end_block; i++) {
            __m128i prev_data = _mm_loadu_si128((__m128i*)&worker.prev_chunk[i * 16]);
            _mm_storeu_si128((__m128i*)&worker.chunk[i * 16], prev_data);
        }

        if (debugOpOrder) printf("loopd: %03lu %03d < %03d\n", worker.tries, worker.pos2, start_block * 16);
        // Copy the remaining bytes after worker.pos2
        for (int i = worker.pos2; i < start_block * 16; i++) {
          worker.chunk[i] = worker.prev_chunk[i];
        }
        */
      }

      if (debugOpOrder) {
        printf("tries: %03lu chunk_before[  0->%03d]: ", worker.tries, worker.pos2);
        for (int x = 0; x <= worker.pos2+16 && worker.pos2+16 < 256; x++) {
          printf("%02x", worker.chunk[x]);
        }
        printf("\n");
      }

      //for (int x = worker.pos1; x < worker.pos2; x++) {
      //  worker.chunk[x] = worker.prev_chunk[x];
      //}
      
      //for (int x = 0; x < 256; x++) {
      //  worker.chunk[x] = worker.prev_chunk[x];
      //}
      memcpy(worker.chunk, worker.prev_chunk, 256);
      if (debugOpOrder) {
        printf("tries: %03lu  chunk_fixed[  0->%03d]: ", worker.tries, worker.pos2);
        for (int x = 0; x <= worker.pos2+16 && worker.pos2+16 < 256; x++) {
          //printf("%d \n", x);
          printf("%02x", worker.chunk[x]);
        }
        printf("\n");
      }
    }
    
    //printf("tries: %03d step_3[0->%-3d]: ", worker.tries, worker.pos2);
    //for (int x = 0; x < worker.pos2; x++) {
    //  printf("%02x", worker.step_3[x]);
    //}
    //printf("\n");

    //printf("%02d ", worker.op);
    //if(worker.tries > 100) {
    //  break;
    //}

    memcpy(worker.fixme, &worker.chunk[worker.pos2], 16);
    switch (worker.op)
    {
    case 0:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random

        // INSERT_RANDOM_CODE_END
        worker.t1 = worker.chunk[worker.pos1];
        worker.t2 = worker.chunk[worker.pos2];
        worker.chunk[worker.pos1] = reverse_bits(worker.t2);
        worker.chunk[worker.pos2] = reverse_bits(worker.t1);
      }
      break;
    case 1:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);
          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);
          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 2:
    {
        worker.opt[worker.op] = true;
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);
          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
          data = xor_with_bittable(data);
                      
          //worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
          data = reverse_bits(data);
          
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
          data = shift_left_by_int_with_and(data, 3);
          
          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
          data = xor_with_bittable(data);
          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
    }
      break;
    case 3:
    {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = std::rotl(worker.chunk[i], worker.chunk[i]); // rotate  bits by random
          data = rotate_by_self(data);

          //worker.chunk[i] = std::rotl(worker.chunk[i], 3);                // rotate  bits by 3
          data = rotate_bits(data, 3);

          //worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
          data = xor_vectors(data, p2vec);

          //worker.chunk[i] = std::rotl(worker.chunk[i], 1);                // rotate  bits by 1
          data = rotate_bits(data, 1);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
    }
      break;
    case 4:
    {
        worker.opt[worker.op] = true;
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);
          //worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
          data = binary_not(data);
          
          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
          data = shift_right_by_int_with_and(data, 3);

          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
          data = rotate_by_self(data);

          //worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
          data = subtract_xored(data, 97);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
    }
      break;
    case 5:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
          data = xor_with_bittable(data);
          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);
          data = shift_right_by_int_with_and(data, 3);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
    break;
    case 6:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));
          data = rotate_bits(data, 3);
          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);
          //worker.chunk[i] -= (worker.chunk[i] ^ 97);
          data = subtract_xored(data, 97);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 7:
      {
        worker.opt[worker.op] = true;
        memcpy(worker.fixme, &worker.chunk[worker.pos2], 16);
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);

        for (int i = worker.pos1; i < worker.pos2; i += 16) {
            // Load 16 bytes (128 bits) of data from chunk
            uint8x16_t data = vld1q_u8(&worker.chunk[i]);

            //worker.chunk[i] += worker.chunk[i];
            data = add_with_self(data);

            //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
            data = rotate_by_self(data);


            //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
            data = xor_with_bittable(data);

            //worker.chunk[i] = ~worker.chunk[i];
            data = binary_not(data);
            vst1q_u8(&worker.chunk[i], data);

            //data = vmulq_u8(data, data);
            //vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 8:
      {
        worker.opt[worker.op] = true;
        memcpy(worker.fixme, &worker.chunk[worker.pos2], 16);
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);

        for (int i = worker.pos1; i < worker.pos2; i += 16) {
            // Load 16 bytes (128 bits) of data from chunk
            uint8x16_t data = vld1q_u8(&worker.chunk[i]);

            //worker.chunk[i] = ~worker.chunk[i];
            data = binary_not(data);
        
            //worker.chunk[i] = (worker.chunk[i] << 2) | (worker.chunk[i] >> 6);
            data = rotate_bits(data, 2);

            //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
            data = shift_left_by_int_with_and(data, 3);

            vst1q_u8(&worker.chunk[i], data);

            //data = vmulq_u8(data, data);
            //vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 9:
      {
        worker.opt[worker.op] = true;
        memcpy(worker.fixme, &worker.chunk[worker.pos2], 16);
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);

        for (int i = worker.pos1; i < worker.pos2; i += 16) {
            // Load 16 bytes (128 bits) of data from chunk
            uint8x16_t data = vld1q_u8(&worker.chunk[i]);

            data = xor_vectors(data, p2vec);
            //vst1q_u8(&worker.chunk[i], data);

            data = rotate_and_xor(data, 4);
            //vst1q_u8(&worker.chunk[i], data);

            data = shift_right_by_int_with_and(data, 3);
            /*
            // store
            vst1q_u8(&worker.chunk[i], data);
            for(int x = i; x < i+16; x++) {
              worker.chunk[x] = worker.chunk[x] >> (worker.chunk[x] & 3); // shift right
            }
            // load 
            data = vld1q_u8(&worker.chunk[i]);
            */

            data = rotate_and_xor(data, 2);
            vst1q_u8(&worker.chunk[i], data);

            //data = vmulq_u8(data, data);
            //vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 10:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));
          data = rotate_bits(data, 3);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 11:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6));
          data = rotate_bits(data, 6);
          // worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);
          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
          data = rotate_by_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 12:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 13:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);
          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);
          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);
          data = shift_right_by_int_with_and(data, 3);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 14:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);
          data = shift_right_by_int_with_and(data, 3);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 15:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);
          //worker.chunk[i] -= (worker.chunk[i] ^ 97);
          data = subtract_xored(data, 97);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 16:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);
          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 17:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);
          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 18:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> 7);
          data = rotate_bits(data, 1);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 19:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] -= (worker.chunk[i] ^ 97);
          data = subtract_xored(data, 97);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] += worker.chunk[i];     
          data = add_with_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 20:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);
          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);

          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);

          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);

          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 21:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);

          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);

          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);

          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 22:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);
          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));   
          data = rotate_bits(data, 1);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 23:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_bits(data, 4);
          // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
          data = xor_with_bittable(data);
          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 24:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);
          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);
          data = shift_right_by_int_with_and(data, 3);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); 
          data = rotate_bits(data, 5);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 25:
      worker.opt[worker.op] = true;
      for (int i = worker.pos1; i < worker.pos2; i += 16) {
          // Load 16 bytes (128 bits) of data from chunk
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
          data = xor_with_bittable(data);

          //worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));
          data = rotate_bits(data, 3);

          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
          data = rotate_bits_by_vector(data);

          //worker.chunk[i] -= (worker.chunk[i] ^ 97);
          data = subtract_xored(data, 97);

          vst1q_u8(&worker.chunk[i], data);
      }
      memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      break;
    case 26:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
          data = xor_with_bittable(data);
          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);
          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 27:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);
          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 28:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          // TODO: Mult by 4?
          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);
          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 29:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] *= worker.chunk[i];
          data = mul_with_self(data);
          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);
          //worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);
          data = shift_right_by_int_with_and(data, 3);
          //worker.chunk[i] += worker.chunk[i];  
          data = add_with_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 30:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2];
          data = and_vectors(data, p2vec);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 31:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] *= worker.chunk[i];   
          data = mul_with_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 32:
      {
        worker.opt[worker.op] = true;
        for (int i = worker.pos1; i < worker.pos2; i += 16) {
            uint8x16_t data = vld1q_u8(&worker.chunk[i]);
            data = rotate_and_xor(data, 2);
            data = reverse_bits(data);
            data = rotate_bits(data, 3);
            data = rotate_and_xor(data, 2);
            vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 33:
      worker.opt[worker.op] = true;
      memcpy(worker.fixme, &worker.chunk[worker.pos2], 16);
      for (int i = worker.pos1; i < worker.pos2; i += 16) {
          // Load 16 bytes (128 bits) of data from chunk
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          data = rotate_bits_by_vector(data);
          
          //vst1q_u8(&worker.chunk[i], data);

          data = rotate_and_xor(data, 4);
          //vst1q_u8(&worker.chunk[i], data);

          data = reverse_bits(data);
          //vst1q_u8(&worker.chunk[i], data);

          data = vmulq_u8(data, data);
          vst1q_u8(&worker.chunk[i], data);
      }
      memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      break;
    case 34:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] -= (worker.chunk[i] ^ 97);
          data = subtract_xored(data, 97);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);
          data = shift_left_by_int_with_and(data, 3);
          //worker.chunk[i] -= (worker.chunk[i] ^ 97); 
          data = subtract_xored(data, 97);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 35:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] += worker.chunk[i];
          data = add_with_self(data);
          //worker.chunk[i] = ~worker.chunk[i];
          data = binary_not(data);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);
          //worker.chunk[i] ^= worker.chunk[worker.pos2];
          data = xor_vectors(data, p2vec);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 36:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
          data = xor_with_bittable(data);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1)); 
          data = rotate_bits(data, 1);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 37:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] *= worker.chunk[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 38:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 39:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 40:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 41:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
        worker.chunk[i] -= (worker.chunk[i] ^ 97);        // XOR and -
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 42:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 1
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 43:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 44:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 45:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 2) | (worker.chunk[i] >> 6);
        // worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                       // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 46:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] += worker.chunk[i];                 // +
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 47:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 48:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        // worker.chunk[i] = ~worker.chunk[i];                    // binary NOT operator
        // worker.chunk[i] = ~worker.chunk[i];                    // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); // rotate  bits by 5
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 49:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] += worker.chunk[i];                 // +
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 50:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);     // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        worker.chunk[i] += worker.chunk[i];              // +
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1)); // rotate  bits by 1
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 51:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 52:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 53:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                 // +
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 54:

#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);  // reverse bits
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
        // worker.chunk[i] = ~worker.chunk[i];    // binary NOT operator
        // worker.chunk[i] = ~worker.chunk[i];    // binary NOT operator
        // INSERT_RANDOM_CODE_END
      }

      break;
    case 55:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 56:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));  // rotate  bits by 1
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 57:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        //worker.chunk[i] = std::rotl(worker.chunk[i], 8); // no-op                // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = reverse_bits(worker.chunk[i]); // reverse bits
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 58:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] += worker.chunk[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 59:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 60:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];    // XOR
        worker.chunk[i] = ~worker.chunk[i];              // binary NOT operator
        worker.chunk[i] *= worker.chunk[i];              // *
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 61:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        //worker.chunk[i] = std::rotl(worker.chunk[i], 8);             // rotate  bits by 3
        // worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));// rotate  bits by 5
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 62:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] += worker.chunk[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 63:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] += worker.chunk[i];                 // +
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 64:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] = reverse_bits(worker.chunk[i]);      // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] *= worker.chunk[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 65:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        //worker.chunk[i] = std::rotl(worker.chunk[i], 8); // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] *= worker.chunk[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 66:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);

          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);

          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);

          //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));
          data = rotate_bits(data, 1);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 67:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));   // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 68:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 69:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 70:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 71:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 72:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 73:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 74:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 75:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 76:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 77:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 78:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 79:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] += worker.chunk[i];               // +
        worker.chunk[i] *= worker.chunk[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 80:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 81:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 82:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
        // worker.chunk[i] = ~worker.chunk[i];        // binary NOT operator
        // worker.chunk[i] = ~worker.chunk[i];        // binary NOT operator
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 83:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        //worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        //worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 84:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] += worker.chunk[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 85:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 86:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 87:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];               // +
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] += worker.chunk[i];               // +
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 88:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));  // rotate  bits by 1
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 89:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];               // +
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 90:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);     // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6)); // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 91:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 92:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 93:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] += worker.chunk[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 94:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 95:
    {
      worker.opt[worker.op] = true;
      for (int i = worker.pos1; i < worker.pos2; i+=16)
      {
        uint8x16_t vec = vld1q_u8(&worker.chunk[i]);

        // Shift the vector elements to the left by one position
        uint8x16_t shifted_left = vshlq_n_u8(vec, 1);
        uint8x16_t shifted_right = vshrq_n_u8(vec, 8-1);
        uint8x16_t rotated = vorrq_u8(shifted_left, shifted_right);
        //worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));  // rotate  bits by 1
      
        //worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
        uint8x16_t data = binary_not(rotated);vmvnq_u8(rotated);        
        
        uint8x16_t shifted_a = rotate_bits(data, 10);
        //worker.chunk[i] = std::rotl(worker.chunk[i], 10);

        vst1q_u8(&worker.chunk[i], shifted_a);
      }
      //memcpy(&worker.chunk[worker.pos2], fixme, (worker.pos2-worker.pos1)%16);
      memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
    }
      break;
    case 96:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));   // rotate  bits by 2
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));   // rotate  bits by 2
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 97:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 98:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 99:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 100:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 101:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 102:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        worker.chunk[i] -= (worker.chunk[i] ^ 97);       // XOR and -
        worker.chunk[i] += worker.chunk[i];              // +
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 103:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 104:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] += worker.chunk[i];                 // +
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 105:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 106:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);      // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));  // rotate  bits by 1
        worker.chunk[i] *= worker.chunk[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 107:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6));             // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 108:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 109:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 110:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 111:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 112:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        worker.chunk[i] = ~worker.chunk[i];              // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); // rotate  bits by 5
        worker.chunk[i] -= (worker.chunk[i] ^ 97);       // XOR and -
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 113:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6)); // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                           // rotate  bits by 1
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = ~worker.chunk[i];                 // binary NOT operator
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 114:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 115:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 116:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 117:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 118:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 119:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);      // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 120:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] = reverse_bits(worker.chunk[i]);      // reverse bits
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 121:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] *= worker.chunk[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 122:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
          data = rotate_by_self(data);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = data = rotate_and_xor(data, 2);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 123:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6));                // rotate  bits by 3
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 124:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 125:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 126:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> 7);
        // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1)); // rotate  bits by 1
        // worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); // rotate  bits by 5
        worker.chunk[i] = reverse_bits(worker.chunk[i]); // reverse bits
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 127:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 128:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
          data = rotate_by_self(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));
          data = rotate_bits(data, 5);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 129:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 130:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 131:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] *= worker.chunk[i];                 // *
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 132:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 133:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 134:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 135:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 136:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 137:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 138:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
        worker.chunk[i] += worker.chunk[i];           // +
        worker.chunk[i] -= (worker.chunk[i] ^ 97);    // XOR and -
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 139:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        //worker.chunk[i] = std::rotl(worker.chunk[i], 8); // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 140:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));  // rotate  bits by 1
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 141:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] += worker.chunk[i];                 // +
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 142:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 143:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 144:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 145:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));
          data = rotate_and_xor(data, 2);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 146:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 147:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] *= worker.chunk[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 148:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 149:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
        worker.chunk[i] = reverse_bits(worker.chunk[i]);  // reverse bits
        worker.chunk[i] -= (worker.chunk[i] ^ 97);    // XOR and -
        worker.chunk[i] += worker.chunk[i];           // +
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 150:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 151:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 152:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 153:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 1
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        // worker.chunk[i] = ~worker.chunk[i];     // binary NOT operator
        // worker.chunk[i] = ~worker.chunk[i];     // binary NOT operator
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 154:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] = ~worker.chunk[i];                 // binary NOT operator
        worker.chunk[i] ^= worker.chunk[worker.pos2];       // XOR
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 155:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] ^= worker.chunk[worker.pos2];       // XOR
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] ^= worker.chunk[worker.pos2];       // XOR
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 156:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));             // rotate  bits by 3
        // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 157:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 158:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));    // rotate  bits by 3
        worker.chunk[i] += worker.chunk[i];                 // +
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 159:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 160:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));             // rotate  bits by 1
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));    // rotate  bits by 3
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 161:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 162:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] = reverse_bits(worker.chunk[i]);      // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] -= (worker.chunk[i] ^ 97);        // XOR and -
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 163:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 164:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];                 // *
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] = ~worker.chunk[i];                 // binary NOT operator
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 165:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] += worker.chunk[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 166:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        worker.chunk[i] += worker.chunk[i];               // +
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 167:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        // worker.chunk[i] = ~worker.chunk[i];        // binary NOT operator
        // worker.chunk[i] = ~worker.chunk[i];        // binary NOT operator
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 168:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 169:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 170:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] -= (worker.chunk[i] ^ 97);   // XOR and -
        worker.chunk[i] = reverse_bits(worker.chunk[i]); // reverse bits
        worker.chunk[i] -= (worker.chunk[i] ^ 97);   // XOR and -
        worker.chunk[i] *= worker.chunk[i];          // *
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 171:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));    // rotate  bits by 3
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 172:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 173:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] += worker.chunk[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 174:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 175:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        worker.chunk[i] -= (worker.chunk[i] ^ 97);       // XOR and -
        worker.chunk[i] *= worker.chunk[i];              // *
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); // rotate  bits by 5
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 176:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];    // XOR
        worker.chunk[i] *= worker.chunk[i];              // *
        worker.chunk[i] ^= worker.chunk[worker.pos2];    // XOR
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); // rotate  bits by 5
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 177:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 178:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 179:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 180:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 181:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 182:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];    // XOR
        worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6)); // rotate  bits by 1
        // worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));         // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 183:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];        // +
        worker.chunk[i] -= (worker.chunk[i] ^ 97); // XOR and -
        worker.chunk[i] -= (worker.chunk[i] ^ 97); // XOR and -
        worker.chunk[i] *= worker.chunk[i];        // *
                                                     // INSERT_RANDOM_CODE_END
      }
      break;
    case 184:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] *= worker.chunk[i];                          // *
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 185:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 186:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 187:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];    // XOR
        worker.chunk[i] = ~worker.chunk[i];              // binary NOT operator
        worker.chunk[i] += worker.chunk[i];              // +
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 188:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];
          data = xor_with_bittable(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
      break;
    case 189:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] -= (worker.chunk[i] ^ 97);        // XOR and -
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 190:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 191:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 192:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] *= worker.chunk[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 193:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 194:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 195:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));   // rotate  bits by 2
        worker.chunk[i] ^= worker.chunk[worker.pos2];       // XOR
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 196:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 197:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] *= worker.chunk[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 198:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 199:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];           // binary NOT operator
        worker.chunk[i] += worker.chunk[i];           // +
        worker.chunk[i] *= worker.chunk[i];           // *
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 200:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 201:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 202:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 203:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));                // rotate  bits by 1
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 204:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 205:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] += worker.chunk[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 206:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 207:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        //worker.chunk[i] = std::rotl(worker.chunk[i], 8); // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                           // rotate  bits by 3
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 208:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 209:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 210:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));                // rotate  bits by 5
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 211:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 212:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 213:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 214:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 215:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] *= worker.chunk[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 216:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 217:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
        worker.chunk[i] += worker.chunk[i];               // +
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));  // rotate  bits by 1
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 218:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]); // reverse bits
        worker.chunk[i] = ~worker.chunk[i];          // binary NOT operator
        worker.chunk[i] *= worker.chunk[i];          // *
        worker.chunk[i] -= (worker.chunk[i] ^ 97);   // XOR and -
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 219:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 220:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 221:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5)); // rotate  bits by 5
        worker.chunk[i] ^= worker.chunk[worker.pos2];    // XOR
        worker.chunk[i] = ~worker.chunk[i];              // binary NOT operator
        worker.chunk[i] = reverse_bits(worker.chunk[i]);     // reverse bits
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 222:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] *= worker.chunk[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 223:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 224:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));  // rotate  bits by 1
        // worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
      }
      break;
    case 225:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        worker.chunk[i] = ~worker.chunk[i];                          // binary NOT operator
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
      }
      break;
    case 226:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);  // reverse bits
        worker.chunk[i] -= (worker.chunk[i] ^ 97);    // XOR and -
        worker.chunk[i] *= worker.chunk[i];           // *
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 227:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 228:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];          // ones count bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 229:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                // rotate  bits by 3
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));               // rotate  bits by 2
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 230:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 231:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] ^= worker.chunk[worker.pos2];                // XOR
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 232:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4)); // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 233:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));    // rotate  bits by 3
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 234:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3);    // shift right
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 235:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] *= worker.chunk[i];               // *
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 236:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= worker.chunk[worker.pos2];                   // XOR
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 237:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));             // rotate  bits by 3
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 238:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];              // +
        worker.chunk[i] += worker.chunk[i];              // +
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3)); // rotate  bits by 3
        worker.chunk[i] -= (worker.chunk[i] ^ 97);       // XOR and -
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 239:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 6) | (worker.chunk[i] >> (8 - 6)); // rotate  bits by 5
        // worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1)); // rotate  bits by 1
        worker.chunk[i] *= worker.chunk[i];                             // *
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 240:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                             // binary NOT operator
        worker.chunk[i] += worker.chunk[i];                             // +
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 241:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));   // rotate  bits by 4
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] ^= worker.chunk[worker.pos2];       // XOR
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 242:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];           // +
        worker.chunk[i] += worker.chunk[i];           // +
        worker.chunk[i] -= (worker.chunk[i] ^ 97);    // XOR and -
        worker.chunk[i] ^= worker.chunk[worker.pos2]; // XOR
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 243:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));   // rotate  bits by 2
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 244:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = reverse_bits(worker.chunk[i]);      // reverse bits
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 245:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] -= (worker.chunk[i] ^ 97);                   // XOR and -
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));             // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 246:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                          // +
        worker.chunk[i] = (worker.chunk[i] << 1) | (worker.chunk[i] >> (8 - 1));             // rotate  bits by 1
        worker.chunk[i] = worker.chunk[i] >> (worker.chunk[i] & 3); // shift right
        worker.chunk[i] += worker.chunk[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 247:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));  // rotate  bits by 5
        worker.chunk[i] = ~worker.chunk[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 248:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = ~worker.chunk[i];                 // binary NOT operator
        worker.chunk[i] -= (worker.chunk[i] ^ 97);          // XOR and -
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 5) | (worker.chunk[i] >> (8 - 5));    // rotate  bits by 5
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 249:
      {
        worker.opt[worker.op] = true;
        uint8x16_t p2vec = vdupq_n_u8(worker.chunk[worker.pos2]);
        for (int i = worker.pos1; i < worker.pos2; i+=16)
        {
          uint8x16_t data = vld1q_u8(&worker.chunk[i]);

          //worker.chunk[i] = reverse_bits(worker.chunk[i]);
          data = reverse_bits(data);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));
          data = rotate_and_xor(data, 4);
          //worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8)));
          data = rotate_by_self(data);

          vst1q_u8(&worker.chunk[i], data);
        }
        memcpy(&worker.chunk[worker.pos2], worker.fixme, 16);
      }
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                    // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 250:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = worker.chunk[i] & worker.chunk[worker.pos2]; // AND
        worker.chunk[i] = (worker.chunk[i] << (worker.chunk[i] % 8)) | (worker.chunk[i] >> (8 - (worker.chunk[i] % 8))); // rotate  bits by random
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]];             // ones count bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));               // rotate  bits by 4
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 251:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] += worker.chunk[i];                 // +
        worker.chunk[i] ^= (byte)bitTable[worker.chunk[i]]; // ones count bits
        worker.chunk[i] = reverse_bits(worker.chunk[i]);        // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));   // rotate  bits by 2
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 252:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = reverse_bits(worker.chunk[i]);                 // reverse bits
        worker.chunk[i] ^= (worker.chunk[i] << 4) | (worker.chunk[i] >> (8 - 4));            // rotate  bits by 4
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));            // rotate  bits by 2
        worker.chunk[i] = worker.chunk[i] << (worker.chunk[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 253:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2)); // rotate  bits by 2
        worker.chunk[i] ^= worker.chunk[worker.pos2];     // XOR
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));  // rotate  bits by 3
        // INSERT_RANDOM_CODE_END

        worker.prev_lhash = worker.lhash + worker.prev_lhash;
        worker.lhash = XXHash64::hash(worker.chunk, worker.pos2,0);
      }
      break;
    case 254:
    case 255:
      RC4_set_key(&worker.key, 256,  worker.chunk);
// worker.chunk = highwayhash.Sum(worker.chunk[:], worker.chunk[:])
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.chunk[i] ^= static_cast<uint8_t>(std::bitset<8>(worker.chunk[i]).count()); // ones count bits
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                                  // rotate  bits by 3
        worker.chunk[i] ^= (worker.chunk[i] << 2) | (worker.chunk[i] >> (8 - 2));                                 // rotate  bits by 2
        worker.chunk[i] = (worker.chunk[i] << 3) | (worker.chunk[i] >> (8 - 3));                                  // rotate  bits by 3
                                                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    default:
      break;
    }

    if(isTest) {
      break;
    }

    // if (op == 53) {
    //   std::cout << hexStr(worker.step_3, 256) << std::endl << std::endl;
    //   std::cout << hexStr(&worker.step_3[worker.pos1], 1) << std::endl;
    //   std::cout << hexStr(&worker.step_3[worker.pos2], 1) << std::endl;
    // }

    __builtin_prefetch(worker.chunk,0,3);
    // __builtin_prefetch(worker.chunk+64,0,3);
    // __builtin_prefetch(worker.chunk+128,0,3);
    __builtin_prefetch(worker.chunk+192,0,3);

    if (debugOpOrder) {
      printf("tries: %03lu  chunk_after[  0->%03d]: ", worker.tries, worker.pos2);
      for (int x = 0; x <= worker.pos2+16 && worker.pos2+16 < 256; x++) {
        printf("%02x", worker.chunk[x]);
      }
      printf("\n");
    }
    if (debugOpOrder && sus_op == worker.op) {
      break;
    }
    if (worker.op == sus_op && debugOpOrder) printf(" CPU: A: c[%02d] %02x c[%02d] %02x\n", worker.pos1, worker.chunk[worker.pos1], worker.pos2, worker.chunk[worker.pos2]);
    worker.A = (worker.chunk[worker.pos1] - worker.chunk[worker.pos2]);
    worker.A = (256 + (worker.A % 256)) % 256;

    if (worker.A < 0x10)
    { // 6.25 % probability
      worker.prev_lhash = worker.lhash + worker.prev_lhash;
      worker.lhash = XXHash64::hash(worker.chunk, worker.pos2, 0);

      // uint64_t test = XXHash64::hash(worker.step_3, worker.pos2, 0);
      if (worker.op == sus_op && debugOpOrder) printf(" CPU: A: new worker.lhash: %08jx\n", worker.lhash);
    }

    if (worker.A < 0x20)
    { // 12.5 % probability
      worker.prev_lhash = worker.lhash + worker.prev_lhash;
      worker.lhash = hash_64_fnv1a(worker.chunk, worker.pos2);

      // uint64_t test = hash_64_fnv1a(worker.step_3, worker.pos2);
      if (worker.op == sus_op && debugOpOrder) printf(" CPU: B: new worker.lhash: %08jx\n", worker.lhash);
    }

    if (worker.A < 0x30)
    { // 18.75 % probability
      worker.prev_lhash = worker.lhash + worker.prev_lhash;
      HH_ALIGNAS(16)
      const highwayhash::HH_U64 key2[2] = {worker.tries, worker.prev_lhash};
      worker.lhash = highwayhash::SipHash(key2, (char*)worker.chunk, worker.pos2); // more deviations

      // uint64_t test = highwayhash::SipHash(key2, (char*)worker.step_3, worker.pos2); // more deviations
      if (worker.op == sus_op && debugOpOrder) printf(" CPU: C: new worker.lhash: %08jx\n", worker.lhash);
    }

    if (worker.A <= 0x40)
    { // 25% probablility
      // if (debugOpOrder && worker.op == sus_op) {
      //   printf("SIMD: D: RC4 key:\n");
      //   for (int i = 0; i < 256; i++) {
      //     printf("%d, ", worker.key.data[i]);
      //   }
      // }
      RC4(&worker.key, 256, worker.chunk, worker.chunk);
    }

    worker.chunk[255] = worker.chunk[255] ^ worker.chunk[worker.pos1] ^ worker.chunk[worker.pos2];

    // if (debugOpOrder && worker.op == sus_op) {
    //   printf("SIMD op %d result:\n", worker.op);
    //   for (int i = 0; i < 256; i++) {
    //       printf("%02X ", worker.chunk[i]);
    //   } 
    //   printf("\n");
    // }

    // memcpy(&worker.sData[(worker.tries - 1) * 256], worker.step_3, 256);
    
    // std::copy(worker.step_3, worker.step_3 + 256, &worker.sData[(worker.tries - 1) * 256]);

    // memcpy(&worker->data.data()[(worker.tries - 1) * 256], worker.step_3, 256);

    // std::cout << hexStr(worker.step_3, 256) << std::endl;

    if (worker.tries > 260 + 16 || (worker.sData[(worker.tries-1)*256+255] >= 0xf0 && worker.tries > 260))
    {
      break;
    }
    if (debugOpOrder) printf("\n\n");
  }
  worker.data_len = static_cast<uint32_t>((worker.tries - 4) * 256 + (((static_cast<uint64_t>(worker.chunk[253]) << 8) | static_cast<uint64_t>(worker.chunk[254])) & 0x3ff));
}

void optest(int op, workerData &worker, byte testData[32], OpTestResult &testRes, int debug_op) {
  // Set us up the bomb
  memset(worker.step_3, 0, 256);
  memcpy(worker.step_3, testData, 255);
  if (debug_op != -1 && debug_op == op) {
    printf("Scalar: %03d -> %03d\n", worker.pos1, worker.pos2);
    printf("SC Input %3d  : ", op);
    for (int i = worker.pos1; i < worker.pos2 + 24 && i < 255; i++) {
      if(i == worker.pos2) {
        printf("  ");
      }
      printf("%02X ", worker.step_3[i]);
    }
    printf("\n");
  }

  auto start = std::chrono::steady_clock::now();
  for(int n = 0; n < 256; n++){
        switch (op)
    {
    case 0:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random

        // INSERT_RANDOM_CODE_END
        worker.t1 = worker.step_3[worker.pos1];
        worker.t2 = worker.step_3[worker.pos2];
        worker.step_3[worker.pos1] = reverse8(worker.t2);
        worker.step_3[worker.pos2] = reverse8(worker.t1);
      }
      break;
    case 1:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] += worker.step_3[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 2:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 3:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 4:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 5:
    {
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {

        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right

        // INSERT_RANDOM_CODE_END
      }
    }
    break;
    case 6:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -

        // INSERT_RANDOM_CODE_END
      }
      break;
    case 7:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 8:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 10); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5);// rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 9:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 10:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
        worker.step_3[i] *= worker.step_3[i];              // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        worker.step_3[i] *= worker.step_3[i];              // *
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 11:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 6); // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5);            // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 12:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 13:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 14:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 15:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 16:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 17:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] *= worker.step_3[i];              // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 18:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 9);  // rotate  bits by 3
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5);         // rotate  bits by 5
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 19:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 20:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 21:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 22:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 23:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 4); // rotate  bits by 3
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1);                           // rotate  bits by 1
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 24:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 25:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 26:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                 // *
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] += worker.step_3[i];                 // +
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 27:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 28:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 29:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 30:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 31:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] *= worker.step_3[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 32:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 33:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] *= worker.step_3[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 34:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 35:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];              // +
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 1); // rotate  bits by 1
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 36:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 37:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] *= worker.step_3[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 38:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 39:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 40:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 41:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
        worker.step_3[i] -= (worker.step_3[i] ^ 97);        // XOR and -
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 42:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 4); // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 43:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 44:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 45:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 10); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5);                       // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 46:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] += worker.step_3[i];                 // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 47:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 48:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        // worker.step_3[i] = ~worker.step_3[i];                    // binary NOT operator
        // worker.step_3[i] = ~worker.step_3[i];                    // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 49:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] += worker.step_3[i];                 // +
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 50:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);     // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        worker.step_3[i] += worker.step_3[i];              // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 1); // rotate  bits by 1
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 51:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 52:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 53:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                 // +
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 54:

#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);  // reverse bits
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
        // worker.step_3[i] = ~worker.step_3[i];    // binary NOT operator
        // worker.step_3[i] = ~worker.step_3[i];    // binary NOT operator
        // INSERT_RANDOM_CODE_END
      }

      break;
    case 55:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 56:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 57:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 8);                // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = reverse8(worker.step_3[i]); // reverse bits
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 58:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] += worker.step_3[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 59:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 60:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
        worker.step_3[i] *= worker.step_3[i];              // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 61:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 8);             // rotate  bits by 3
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5);// rotate  bits by 5
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 62:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] += worker.step_3[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 63:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] += worker.step_3[i];                 // +
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 64:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] *= worker.step_3[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 65:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 8); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] *= worker.step_3[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 66:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 67:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 68:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 69:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 70:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 71:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 72:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 73:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 74:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 75:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 76:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 77:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 78:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 79:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] += worker.step_3[i];               // +
        worker.step_3[i] *= worker.step_3[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 80:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 81:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 82:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
        // worker.step_3[i] = ~worker.step_3[i];        // binary NOT operator
        // worker.step_3[i] = ~worker.step_3[i];        // binary NOT operator
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 83:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 84:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 85:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 86:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 87:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];               // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] += worker.step_3[i];               // +
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 88:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 89:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];               // +
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 90:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);     // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 6); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 91:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 92:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 93:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] += worker.step_3[i];                             // +
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 94:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 95:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 10); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 96:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 97:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 98:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 99:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 100:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 101:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 102:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        worker.step_3[i] -= (worker.step_3[i] ^ 97);       // XOR and -
        worker.step_3[i] += worker.step_3[i];              // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 103:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 104:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] += worker.step_3[i];                 // +
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 105:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 106:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
        worker.step_3[i] *= worker.step_3[i];               // *
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 107:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 6);             // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 108:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 109:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 110:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 111:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 112:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
        worker.step_3[i] -= (worker.step_3[i] ^ 97);       // XOR and -
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 113:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 6); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1);                           // rotate  bits by 1
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = ~worker.step_3[i];                 // binary NOT operator
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 114:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 115:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 116:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 117:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 118:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 119:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 120:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 121:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] *= worker.step_3[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 122:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 123:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 6);                // rotate  bits by 3
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 124:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 125:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 126:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 9); // rotate  bits by 3
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1); // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
        worker.step_3[i] = reverse8(worker.step_3[i]); // reverse bits
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 127:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 128:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 129:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 130:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 131:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] *= worker.step_3[i];                 // *
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 132:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 133:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 134:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 135:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 136:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 137:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 138:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
        worker.step_3[i] += worker.step_3[i];           // +
        worker.step_3[i] -= (worker.step_3[i] ^ 97);    // XOR and -
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 139:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 8); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 140:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 141:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] += worker.step_3[i];                 // +
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 142:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 143:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 144:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 145:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 146:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 147:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] *= worker.step_3[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 148:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 149:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
        worker.step_3[i] = reverse8(worker.step_3[i]);  // reverse bits
        worker.step_3[i] -= (worker.step_3[i] ^ 97);    // XOR and -
        worker.step_3[i] += worker.step_3[i];           // +
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 150:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 151:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 152:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 153:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 4); // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        // worker.step_3[i] = ~worker.step_3[i];     // binary NOT operator
        // worker.step_3[i] = ~worker.step_3[i];     // binary NOT operator
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 154:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] = ~worker.step_3[i];                 // binary NOT operator
        worker.step_3[i] ^= worker.step_3[worker.pos2];       // XOR
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 155:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] ^= worker.step_3[worker.pos2];       // XOR
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= worker.step_3[worker.pos2];       // XOR
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 156:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = std::rotl(worker.step_3[i], 4);             // rotate  bits by 3
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 157:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 158:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);    // rotate  bits by 3
        worker.step_3[i] += worker.step_3[i];                 // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 159:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 160:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 4);             // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);    // rotate  bits by 3
        // INSERT_RANDOM_CODE_END
      }
      break;
    case 161:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 162:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] -= (worker.step_3[i] ^ 97);        // XOR and -
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 163:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 164:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                 // *
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] = ~worker.step_3[i];                 // binary NOT operator
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 165:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 166:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] += worker.step_3[i];               // +
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 167:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        // worker.step_3[i] = ~worker.step_3[i];        // binary NOT operator
        // worker.step_3[i] = ~worker.step_3[i];        // binary NOT operator
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 168:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 169:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 170:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);   // XOR and -
        worker.step_3[i] = reverse8(worker.step_3[i]); // reverse bits
        worker.step_3[i] -= (worker.step_3[i] ^ 97);   // XOR and -
        worker.step_3[i] *= worker.step_3[i];          // *
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 171:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);    // rotate  bits by 3
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 172:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 173:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 174:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 175:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        worker.step_3[i] -= (worker.step_3[i] ^ 97);       // XOR and -
        worker.step_3[i] *= worker.step_3[i];              // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 176:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] *= worker.step_3[i];              // *
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 177:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 178:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 179:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 180:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 181:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 182:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 6); // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 5);         // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 183:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];        // +
        worker.step_3[i] -= (worker.step_3[i] ^ 97); // XOR and -
        worker.step_3[i] -= (worker.step_3[i] ^ 97); // XOR and -
        worker.step_3[i] *= worker.step_3[i];        // *
                                                     // INSERT_RANDOM_CODE_END
      }
      break;
    case 184:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] *= worker.step_3[i];                          // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 185:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 186:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 187:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
        worker.step_3[i] += worker.step_3[i];              // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 188:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 189:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] -= (worker.step_3[i] ^ 97);        // XOR and -
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 190:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 191:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 192:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] *= worker.step_3[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 193:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 194:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 195:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
        worker.step_3[i] ^= worker.step_3[worker.pos2];       // XOR
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 196:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 197:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] *= worker.step_3[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 198:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 199:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];           // binary NOT operator
        worker.step_3[i] += worker.step_3[i];           // +
        worker.step_3[i] *= worker.step_3[i];           // *
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 200:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 201:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 202:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 203:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);                // rotate  bits by 1
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 204:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 205:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 206:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 207:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 8); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);                           // rotate  bits by 3
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 208:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 209:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 210:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);                // rotate  bits by 5
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 211:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 212:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 213:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 214:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 215:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] *= worker.step_3[i];                             // *
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 216:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 217:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
        worker.step_3[i] += worker.step_3[i];               // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);  // rotate  bits by 1
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 218:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]); // reverse bits
        worker.step_3[i] = ~worker.step_3[i];          // binary NOT operator
        worker.step_3[i] *= worker.step_3[i];          // *
        worker.step_3[i] -= (worker.step_3[i] ^ 97);   // XOR and -
                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 219:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 220:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 221:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5); // rotate  bits by 5
        worker.step_3[i] ^= worker.step_3[worker.pos2];    // XOR
        worker.step_3[i] = ~worker.step_3[i];              // binary NOT operator
        worker.step_3[i] = reverse8(worker.step_3[i]);     // reverse bits
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 222:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] *= worker.step_3[i];                          // *
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 223:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 224:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 4);  // rotate  bits by 1
        // worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       //
      }
      break;
    case 225:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                          // binary NOT operator
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 226:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);  // reverse bits
        worker.step_3[i] -= (worker.step_3[i] ^ 97);    // XOR and -
        worker.step_3[i] *= worker.step_3[i];           // *
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 227:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 228:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];          // ones count bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 229:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                // rotate  bits by 3
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);               // rotate  bits by 2
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 230:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 231:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] ^= worker.step_3[worker.pos2];                // XOR
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 232:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4); // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 233:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);    // rotate  bits by 3
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 234:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3);    // shift right
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 235:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] *= worker.step_3[i];               // *
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 236:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= worker.step_3[worker.pos2];                   // XOR
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                      // XOR and -
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 237:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);             // rotate  bits by 3
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 238:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];              // +
        worker.step_3[i] += worker.step_3[i];              // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 3); // rotate  bits by 3
        worker.step_3[i] -= (worker.step_3[i] ^ 97);       // XOR and -
                                                           // INSERT_RANDOM_CODE_END
      }
      break;
    case 239:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 6); // rotate  bits by 5
        // worker.step_3[i] = std::rotl(worker.step_3[i], 1); // rotate  bits by 1
        worker.step_3[i] *= worker.step_3[i];                             // *
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 240:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                             // binary NOT operator
        worker.step_3[i] += worker.step_3[i];                             // +
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3);    // shift left
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 241:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);   // rotate  bits by 4
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] ^= worker.step_3[worker.pos2];       // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 242:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];           // +
        worker.step_3[i] += worker.step_3[i];           // +
        worker.step_3[i] -= (worker.step_3[i] ^ 97);    // XOR and -
        worker.step_3[i] ^= worker.step_3[worker.pos2]; // XOR
                                                        // INSERT_RANDOM_CODE_END
      }
      break;
    case 243:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);    // rotate  bits by 1
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 244:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = reverse8(worker.step_3[i]);      // reverse bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 245:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] -= (worker.step_3[i] ^ 97);                   // XOR and -
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);             // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 246:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                          // +
        worker.step_3[i] = std::rotl(worker.step_3[i], 1);             // rotate  bits by 1
        worker.step_3[i] = worker.step_3[i] >> (worker.step_3[i] & 3); // shift right
        worker.step_3[i] += worker.step_3[i];                          // +
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 247:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);  // rotate  bits by 5
        worker.step_3[i] = ~worker.step_3[i];               // binary NOT operator
                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    case 248:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = ~worker.step_3[i];                 // binary NOT operator
        worker.step_3[i] -= (worker.step_3[i] ^ 97);          // XOR and -
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 5);    // rotate  bits by 5
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 249:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);                    // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 250:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = worker.step_3[i] & worker.step_3[worker.pos2]; // AND
        worker.step_3[i] = std::rotl(worker.step_3[i], worker.step_3[i]); // rotate  bits by random
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]];             // ones count bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);               // rotate  bits by 4
                                                                          // INSERT_RANDOM_CODE_END
      }
      break;
    case 251:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] += worker.step_3[i];                 // +
        worker.step_3[i] ^= (byte)bitTable[worker.step_3[i]]; // ones count bits
        worker.step_3[i] = reverse8(worker.step_3[i]);        // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);   // rotate  bits by 2
                                                              // INSERT_RANDOM_CODE_END
      }
      break;
    case 252:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = reverse8(worker.step_3[i]);                 // reverse bits
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 4);            // rotate  bits by 4
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);            // rotate  bits by 2
        worker.step_3[i] = worker.step_3[i] << (worker.step_3[i] & 3); // shift left
                                                                       // INSERT_RANDOM_CODE_END
      }
      break;
    case 253:
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2); // rotate  bits by 2
        worker.step_3[i] ^= worker.step_3[worker.pos2];     // XOR
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);  // rotate  bits by 3
        // INSERT_RANDOM_CODE_END

        worker.prev_lhash = worker.lhash + worker.prev_lhash;
        worker.lhash = XXHash64::hash(worker.step_3, worker.pos2,0);
      }
      break;
    case 254:
    case 255:
      RC4_set_key(&worker.key, 256,  worker.step_3);
// worker.step_3 = highwayhash.Sum(worker.step_3[:], worker.step_3[:])
#pragma GCC unroll 32
      for (int i = worker.pos1; i < worker.pos2; i++)
      {
        // INSERT_RANDOM_CODE_START
        worker.step_3[i] ^= static_cast<uint8_t>(std::bitset<8>(worker.step_3[i]).count()); // ones count bits
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                                  // rotate  bits by 3
        worker.step_3[i] ^= std::rotl(worker.step_3[i], 2);                                 // rotate  bits by 2
        worker.step_3[i] = std::rotl(worker.step_3[i], 3);                                  // rotate  bits by 3
                                                                                            // INSERT_RANDOM_CODE_END
      }
      break;
    default:
      break;
    }
}
  auto end = std::chrono::steady_clock::now();
  auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);
  testRes.duration_ns = time;
  memcpy(testRes.result, worker.step_3, 256);
  if (debug_op != -1 && debug_op == op) {
    printf("SC result     : ");
    for (int i = worker.pos1; i < worker.pos2 + 24 && i < 255; i++) {
      if(i == worker.pos2) {
        printf("  ");
      }
      printf("%02x ", worker.step_3[i]);
    }
    printf("\n took %ld ns\n---------------\n", time.count());
  }
}


void optest_aarch64(int op, workerData &worker, byte testData[32], OpTestResult &testRes, int debug_op) {
  // chunk (a pointer) now points to step_3[0] (which holds the data)
  worker.chunk = worker.step_3;
  // Set us up the bomb
  memset(worker.chunk, 0, 256);
  memcpy(worker.chunk, testData, 255);

  if (debug_op != -1 && debug_op == op) {
    printf("AA64  : %03d -> %03d\n", worker.pos1, worker.pos2);
    printf("AA64 Input %3d: ", op);
    for (int i = worker.pos1; i < (worker.pos2 + 24) && i < 255; i++) {
      if(i == worker.pos2) {
        printf("  ");
      }
      printf("%02X ", worker.chunk[i]);
    }
    printf("\n");
  }

  auto start = std::chrono::steady_clock::now();
  for(int x = 0; x < 256; x++) {
    worker.op = op;
    //worker.pos1 = 0; worker.pos2 = 16;
    //worker.pos1 = 0; worker.pos2 = 32;
    //worker.chunk = worker.step_3;
    //worker.prev_chunk = worker.chunk;
    branchComputeCPU_aarch64(worker, true);
  }

  auto test_end = std::chrono::steady_clock::now();
  auto test_time = std::chrono::duration_cast<std::chrono::nanoseconds>(test_end-start);
  testRes.duration_ns = test_time;
  memcpy(testRes.result, worker.chunk, 256);
  //memcpy(testRes.result, worker.salsaInput, 256);
  if (debug_op != -1 && debug_op == op) {
    printf("AA64 result   : ");
    for (int i = worker.pos1; i < worker.pos2 + 24 && i < 255; i++) {
      if(i == worker.pos2) {
        printf("  ");
      }
      printf("%02x ", worker.chunk[i]);
    }
    printf("\n took %ld ns\n---------------\n", test_time.count());
  }
  return; 
}



int runDeroVerificationTests(bool useLookup, int dataLen=15, int debug_op=-1) {
  if(dataLen == -1 || dataLen > 255) {
    dataLen = 32;
  }
  int max_op = 255;
  if(debug_op != -1) {
    max_op = debug_op;
  }
  int numOpsFailed = 0;
  #if defined(__AVX2__)
  testPopcnt256_epi8();
  #endif

  workerData *controlWorker = new workerData;
  //initWorker(*controlWorker);
  //lookupGen(*controlWorker, nullptr, nullptr);

  workerData *testWorker = new workerData;
  //initWorker(*testWorker);
  //lookupGen(*testWorker, nullptr, nullptr);

  byte test[255];
  generateInitVector<255>(test);
  //generateRandomBytes<255>(test);

  printf("Initial Input\n");
  for (int i = 0; i < dataLen; i++) {
    printf("%02x ", test[i]);
  }
  printf("\n");

  //int max_op = 255;
  //int data_len = 48;
  for(int op = 0; op <= max_op; op++) {
    // WARMUP, don't print times
    OpTestResult *controlResult = new OpTestResult;
    OpTestResult *testResult = new OpTestResult;
    // WARMUP, don't print times

    controlWorker->pos1 = 0; controlWorker->pos2 = 16;
    //memset(&controlWorker->step_3, 0, 256);
    //memcpy(&controlWorker->step_3, test, dataLen);
    optest(0, *controlWorker, test, *controlResult, -1);

    controlWorker->pos1 = 0; controlWorker->pos2 = 24;
    //memset(&controlWorker->step_3, 0, 256);
    //memcpy(&controlWorker->step_3, test, dataLen);
    optest(op, *controlWorker, test, *controlResult, debug_op);
    //printf("  Op: %3d - %6ld ns\n", op, controlResult->duration_ns);

    testWorker->pos1 = 0; testWorker->pos2 = 24;

      #ifdef __X86_64__
      optest_avx2(op, *testWorker, test, *testResult, false);
      #else
      optest_aarch64(op, *testWorker, test, *testResult, debug_op);
      #endif
    

    auto control_dur = controlResult->duration_ns.count();
    auto test_dur = testResult->duration_ns.count();

    auto percent_speedup = double(double(control_dur-test_dur)/double(test_dur))*100;
    bool valid = 0 == memcmp(controlResult->result, testResult->result, dataLen);
    char isOpt = ' ';
    if(testWorker->opt[op]) {
      isOpt = '*';
    }
    printf("%cOp: %3d - %6ld ns / %6ld ns = %6.2f %% - %s\n", isOpt, op, controlResult->duration_ns.count(), testResult->duration_ns.count(), percent_speedup, valid ? "true" : "false");
    if(!valid) {
      numOpsFailed++;
      printf("Vanilla: ");
      for (int i = 0; i < dataLen; i++) {
        printf("%02x", controlResult->result[i]);
      }
      printf("\n");
      if(useLookup) {
        printf(" Lookup: ");
      } else {
        #ifdef __X86_64__
        printf("   SIMD: ");
        #else
        printf("AArch64: ");
        #endif
      }

      for (int i = 0; i < dataLen; i++) {
        printf("%02x", testResult->result[i]);
      }
      printf("\n");
    }
  }

  return numOpsFailed;
}


struct PowTest{
	std::string out;
	std::string in;
	bool expectFail = false;
};

inline PowTest random_pow_tests[] = {
	{"54e2324ddacc3f0383501a9e5760f85d63e9bc6705e9124ca7aef89016ab81ea", "a"},
	{"faeaff767be60134f0bcc5661b5f25413791b4df8ad22ff6732024d35ec4e7d0", "ab"},
	{"715c3d8c61a967b7664b1413f8af5a2a9ba0005922cb0ba4fac8a2d502b92cd6", "abc"},
	{"74cc16efc1aac4768eb8124e23865da4c51ae134e29fa4773d80099c8bd39ab8", "abcd"},
	{"d080d0484272d4498bba33530c809a02a4785368560c5c3eac17b5dacd357c4b", "abcde"},
	{"813e89e0484cbd3fbb3ee059083af53ed761b770d9c245be142c676f669e4607", "abcdef"}, 
	{"3972fe8fe2c9480e9d4eff383b160e2f05cc855dc47604af37bc61fdf20f21ee", "abcdefg"},
	{"f96191b7e39568301449d75d42d05090e41e3f79a462819473a62b1fcc2d0997", "abcdefgh"},
	{"8c76af6a57dfed744d5b7467fa822d9eb8536a851884aa7d8e3657028d511322", "abcdefghi"},
	{"f838568c38f83034b2ff679d5abf65245bd2be1b27c197ab5fbac285061cf0a7", "abcdefghij"},
	{"ff9f23980870b4dd3521fcf6807b85d8bf70c5fbbd9736c87c23fac0114e2b8b", "4145bd000025fbf83b29cddc000000009b6d4f3ecaaaea9e99ff5630b7c9d01d000000000e326f0593a9000000339a10", true}
};


inline void hashSHA256(SHA256_CTX &sha256, const byte *input, byte *digest, unsigned long inputSize)
{
  SHA256_Init(&sha256);
  SHA256_Update(&sha256, input, inputSize);
  SHA256_Final(digest, &sha256);
}


void AstroBWTv3(byte *input, int inputLen, byte *outputhash, workerData &worker, bool lookupMine)
{
  // auto recoverFunc = [&outputhash](void *r)
  // {
  //   std::random_device rd;
  //   std::mt19937 gen(rd());
  //   std::uniform_int_distribution<uint8_t> dist(0, 255);
  //   std::array<uint8_t, 16> buf;
  //   std::generate(buf.begin(), buf.end(), [&dist, &gen]()
  //                 { return dist(gen); });
  //   std::memcpy(outputhash, buf.data(), buf.size());
  //   std::cout << "exception occured, returning random hash" << std::endl;
  // };
  // std::function<void(void *)> recover = recoverFunc;

  try
  {
    std::fill_n(worker.sData + 256, 64, 0);

    __builtin_prefetch(&worker.sData[256], 1, 3);
    __builtin_prefetch(&worker.sData[256+64], 1, 3);
    __builtin_prefetch(&worker.sData[256+128], 1, 3);
    __builtin_prefetch(&worker.sData[256+192], 1, 3);
    
    hashSHA256(worker.sha256, input, &worker.sData[320], inputLen);
    worker.salsa20.setKey(&worker.sData[320]);
    worker.salsa20.setIv(&worker.sData[256]);

    __builtin_prefetch(worker.sData, 1, 3);
    __builtin_prefetch(&worker.sData[64], 1, 3);
    __builtin_prefetch(&worker.sData[128], 1, 3);
    __builtin_prefetch(&worker.sData[192], 1, 3);

    worker.salsa20.processBytes(worker.salsaInput, worker.sData, 256);

    __builtin_prefetch(&worker.key + 8, 1, 3);
    __builtin_prefetch(&worker.key + 8+64, 1, 3);
    __builtin_prefetch(&worker.key + 8+128, 1, 3);
    __builtin_prefetch(&worker.key + 8+192, 1, 3);

    RC4_set_key(&worker.key, 256,  worker.sData);
    RC4(&worker.key, 256, worker.sData,  worker.sData);

    worker.lhash = hash_64_fnv1a_256(worker.sData);
    worker.prev_lhash = worker.lhash;

    worker.tries = 0;
    
    if(debugOpOrder) {
      printf("sData before: ");
      printf("%s", hexStr(worker.sData, 128).c_str());
      printf("\n");
    }
    
    // auto start = std::chrono::steady_clock::now();
    // auto end = std::chrono::steady_clock::now();


      // start = std::chrono::steady_clock::now();
 #if defined(__AVX2__)
      branchComputeCPU_avx2(worker);
 #else
      branchComputeCPU_aarch64(worker, false);
 #endif
      // end = std::chrono::steady_clock::now();
    
    

    // auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end-start);
    // if (!lookupMine) printf("AVX2: ");
    // else printf("Lookup: ");
    // printf("branched section took %dns\n", time.count());
    if (debugOpOrder) {
      if (lookupMine) {
        printf("Lookup Table:\n-----------\n");
        for (int i = 0; i < worker.opsB.size(); i++) {
          printf("%d, ", worker.opsB[i]);
        }
      } else {
        printf("Scalar:\n-----------\n");
        for (int i = 0; i < worker.opsA.size(); i++) {
          printf("%d, ", worker.opsA[i]);
        }
      }

      printf("\n");
      worker.opsA.clear();
      worker.opsB.clear();
    }
    // // worker.data_len = 70000;
    //saveBufferToFile("worker_sData_snapshot.bin", worker.sData, worker.data_len);
    // printf("data length: %d\n", worker.data_len);
    if(debugOpOrder) {
      printf("data length: %d\n", worker.data_len);
      printf("sData after: ");
      for(int x = 0; x < 48; x++) {
        printf("%02x", worker.sData[x]);
      }
      printf("\n\n");
    }
    divsufsort(worker.sData, worker.sa, worker.data_len, worker.bA, worker.bB);
    // computeByteFrequencyAVX2(worker.sData, worker.data_len, worker.freq);
    // libsais_ctx(worker.ctx, worker.sData, worker.sa, worker.data_len, MAX_LENGTH-worker.data_len, NULL);


    if (littleEndian())
    {
      byte *B = reinterpret_cast<byte *>(worker.sa);
      hashSHA256(worker.sha256, B, worker.sHash, worker.data_len*4);
      // worker.sHash = nHash;
    }
    else
    {
      byte *s = new byte[MAX_LENGTH * 4];
      for (int i = 0; i < worker.data_len; i++)
      {
        s[i << 1] = htonl(worker.sa[i]);
      }
      hashSHA256(worker.sha256, s, worker.sHash, worker.data_len*4);
      // worker.sHash = nHash;
      delete[] s;
    }
    memcpy(outputhash, worker.sHash, 32);
  }
  catch (const std::exception &ex)
  {
    // recover(outputhash);
    std::cerr << ex.what() << std::endl;
  }
}


int TestAstroBWTv3repeattest()
{
  int numTestFail = 0;
  /*
  workerData *worker = (workerData *)malloc_huge_pages(sizeof(workerData));
  initWorker(*worker);
  lookupGen(*worker, lookup2D, lookup3D);

  byte *data = new byte[48];
  byte random_data[48];

  std::string c("419ebb000000001bbdc9bf2200000000635d6e4e24829b4249fe0e67878ad4350000000043f53e5436cf610000086b00");
  hexstrToBytes(c, data);

  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<uint8_t> dist(0, 255);
  std::array<byte, 48> buf;

  for (int i = 0; i < 1024; i++)
  {
    std::generate(buf.begin(), buf.end(), [&dist, &gen]()
                  { return dist(gen); });
    std::memcpy(random_data, buf.data(), buf.size());

    // std::cout << hexStr(data, 48) << std::endl;
    // std::cout << hexStr(random_data, 48) << std::endl;

    if (i % 2 == 0)
    {
      byte res[32];
      AstroBWTv3(data, 48, res, *worker, true);

      // hexStr(res, 64);
      std::string s = hexStr(res, 32);
      if (s != "c392762a462fd991ace791bfe858c338c10c23c555796b50f665b636cb8c8440")
      {
        printf("%d test failed hash %s\n", i, s.c_str());
        numTestFail=1;
      }
    }
    else
    {
      byte res[32];
      AstroBWTv3(buf.data(), 48, res, *worker, false);
    }
  }
  std::cout << "Repeated test over" << std::endl;
  */
  return numTestFail;
}

int TestAstroBWTv3()
{
  int numTestFail = 0;
  std::srand(1);
  int n = -1;
  workerData *worker = (workerData *)malloc_huge_pages(sizeof(workerData));
  //initWorker(*worker);
  //lookupGen(*worker, lookup2D, lookup3D);
  workerData *worker2 = (workerData *)malloc_huge_pages(sizeof(workerData));
  //initWorker(*worker2);
  //lookupGen(*worker2, lookup2D, lookup3D);

  int i = 0;
  for (PowTest t : random_pow_tests)
  {
    if(numTestFail > 0) {
      break;
    }
    // if (i > 0)
    //   break;
    byte *buf = new byte[t.in.size()];
    memcpy(buf, t.in.c_str(), t.in.size());
    byte res[32];
    byte res2[32];
    AstroBWTv3(buf, (int)t.in.size(), res2, *worker, true);
    // printf("vanilla result: %s\n", hexStr(res, 32).c_str());
    AstroBWTv3(buf, (int)t.in.size(), res, *worker2, false);
    // printf("lookup result: %s\n", hexStr(res, 32).c_str());
    std::string s = hexStr(res, 32);
    if (s.c_str() != t.out)
    {
      if(t.expectFail) {
        printf("SUCCESS! Pow function failed as expected! (%s) -> %s != %s\n", t.in.c_str(), s.c_str(), t.out.c_str());
      } else {
        printf("FAIL. Pow function: pow(%s) -> %s != %s\n", t.in.c_str(), s.c_str(), t.out.c_str());
        numTestFail++;
      }

      // Section below is for debugging modifications to the branched compute operation

      // debugOpOrder = true;
      // worker = (workerData *)malloc_huge_pages(sizeof(workerData));
      // initWorker(*worker);
      // lookupGen(*worker, lookup2D, lookup3D);
      // AstroBWTv3(buf, (int)t.in.size(), res2, *worker, false);
      // worker2 = (workerData *)malloc_huge_pages(sizeof(workerData));
      // initWorker(*worker2);
      // lookupGen(*worker2, lookup2D, lookup3D);
      // AstroBWTv3(buf, (int)t.in.size(), res, *worker2, true);
      // debugOpOrder = false;
    }
    else
    {
      printf("SUCCESS! pow(%s) -> %s want %s\n", t.in.c_str(), s.c_str(), t.out.c_str());
    }

    delete[] buf;
    i++;
  }

  byte *data = new byte[48];
  byte *data2 = new byte[48];

  std::string c("7199110000261dfb0b02712100000000c09a113bf2050b1e55c79d15116bd94e00000000a9041027027fa800000314bb");
  std::string c2("7199110000261dfb0b02712100000000c09a113bf2050b1e55c79d15116bd94e00000000a9041027027fa800002388bb");
  hexstrToBytes(c, data);
  hexstrToBytes(c2, data2);

  printf("A: %s, B: %s\n", hexStr(data, 48).c_str(), hexStr(data2, 48).c_str());

  numTestFail += TestAstroBWTv3repeattest();

  // for (int i = 0; i < 1024; i++)
  // {
  //   std::generate(buf.begin(), buf.end(), [&dist, &gen]()
  //                 { return dist(gen); });
  //   std::memcpy(random_data, buf.data(), buf.size());

  //   // std::cout << hexStr(data, 48) << std::endl;
  //   // std::cout << hexStr(random_data, 48) << std::endl;

  //   if (i % 2 == 0)
  //   {
  //     byte res[32];
  //     AstroBWTv3(data, 48, res, *worker, false);

  //     // hexStr(res, 64);
  //     std::string s = hexStr(res, 32);f
  //     if (s != "c392762a462fd991ace791bfe858c338c10c23c555796b50f665b636cb8c8440")
  //     {
  //       printf("%d test failed hash %s\n", i, s.c_str());
  //     }
  //   }
  //   else
  //   {
  //     byte res[32];
  //     AstroBWTv3(buf.data(), 48, res, *worker, false);
  //   }
  // }
  // std::cout << "Repeated test over" << std::endl;
  // libcubwt_free_device_storage(storage);
  // cudaFree(storage);
  return numTestFail;
}



int main(int argc , char* argv[]) {
  int stop_op = -1;
  int test_len = 48;
  workerData *worker = new workerData;

  for(byte x = 0; x < 255; x++) {
      worker->step_3[x] = x;
  }
  worker->chunk = worker->step_3;

  worker->pos1 = 0;
  worker->pos2 = 16;
  auto start = std::chrono::steady_clock::now();
  oldschool(*worker);
  auto test_end = std::chrono::steady_clock::now();
  auto test_time = std::chrono::duration_cast<std::chrono::nanoseconds>(test_end-start);
  printf("old: %5d ns\n", test_time.count());
  for(int x = 0; x < test_len; x++) {
    if(x == worker->pos2) {
      printf("  ");
    }
    printf("%02x ", worker->chunk[x]);
  }
  printf("\n");
  
  for(byte x = 0; x < 255; x++) {
      worker->step_3[x] = x;
  }
  worker->chunk = worker->step_3;
  start = std::chrono::steady_clock::now();
  newschool(*worker);
  test_end = std::chrono::steady_clock::now();
  test_time = std::chrono::duration_cast<std::chrono::nanoseconds>(test_end-start);
  printf("new: %5d ns\n", test_time.count());
  for(int x = 0; x < test_len; x++) {
    if(x == worker->pos2) {
      printf("  ");
    }
    printf("%02x ", worker->chunk[x]);
  }
  printf("\n");
  //return 0;





  printf("argc: %d\n", argc);
  if(argc >= 2) {
    stop_op = atoi(argv[1]);
  }
  printf("stop_op: %d\n", stop_op);
  if(stop_op == 999) {
    return 0;
  }

  
  /*
  for(byte i = 0; i < 255; i++) {
    printf("%02x ", reverse8(i));
    if((i % 65) == 0) {
      printf("\n");
    }
  }
  printf("\n");


  auto start = std::chrono::steady_clock::now();
  for(byte i = 0; i < 255; i++) {
    reverse8(i);
  }
  auto test_end = std::chrono::steady_clock::now();
  auto test_time = std::chrono::duration_cast<std::chrono::nanoseconds>(test_end-start);
  printf("old: %5d ns\n", test_time.count());
  */

  int rc = runDeroVerificationTests(false, test_len, stop_op);
  if(rc != 0) {
    printf("OpTest failed\n");
    return rc;
  }

  return TestAstroBWTv3();
}
