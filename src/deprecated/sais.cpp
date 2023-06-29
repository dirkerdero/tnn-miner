#include <stdint.h>
#include <iostream>

#include <sais2.h>

using byte = unsigned char;

//begin
/*func*/void text_32(byte *text, int32_t *sa, int tLen, int sLen) {
  if ((int)(int32_t)tLen != tLen || tLen != sLen) {
    std::cout << "suffixarray: misuse of text_32" << std::endl;
    return;
  }
  int32_t memory[2*256];
  sais_8_32(text, 256, sa, memory, tLen, sLen, 2*256);
}//end


/*func*/void sais_8_32(byte *text, int textMax, int32_t *sa, int32_t *tmp, int textLen, int saLen, int tmpLen) {
  if (saLen != textLen || tmpLen < textMax) {
    std::cout << "suffixarray: misuse of sais_8_32" << std::endl;
    return;
  }

  if (textLen == 0) {
    return;
  }

  if (textLen == 1) {
    sa[0] = 0;
    return;
  }

  int32_t freq[textMax], bucket[textMax];
  if (tmpLen >= 2*textMax) {
    std::copy(tmp, tmp+textMax, freq);
    std::copy(tmp+textMax, tmp+textMax*2, bucket);
    freq[0] = -1;
  } else {
    std::copy(tmp, tmp+textMax, bucket);
  }

  //SAIS
  int numLMS = placeLMS_8_32(text, sa, freq, bucket, textLen);
  if (numLMS > 1) {
    induceSubL_8_32(text, sa, freq, bucket, textLen, saLen);
    induceSubS_8_32(text, sa, freq, bucket, textLen, saLen);
    length_8_32(text, sa, numLMS, textLen);
    int maxID = assignID_8_32(text, sa, textLen, numLMS, saLen);
    if (maxID < numLMS) {
      map_32(sa, numLMS, saLen);
      recurse_32(sa, tmp, numLMS, maxID, saLen, tmpLen);
      unmap_8_32(text, sa, numLMS, textLen, saLen);
    } else {
      std::copy(sa + (saLen - numLMS), sa + saLen, sa);
    }
    expand_8_32(text, freq, bucket, sa, numLMS, textLen, saLen);
  }
  induceL_8_32(text, sa, freq, bucket, textLen, saLen);
  induceS_8_32(text, sa, freq, bucket, textLen, saLen);

  tmp[0] = -1;
}//end

/*func*/int32_t *freq_8_32(byte *text, int32_t *freq, int32_t *bucket, int tLen) {
  if (freq != nullptr && freq[0] >= 0) {
    return freq;
  }
  if (freq == nullptr) {
    freq = bucket;
  }

  trim256(freq);
  for (int i = 0; i < 256; i++) {
    freq[i] = 0;
  }

  for (int i = 0; i < tLen; i++) {
    if (i >= 256) break;
    freq[text[i]]++;
  }

  return freq;
}//end


/*func*/void bucketMin_8_32(byte *text, int32_t *freq, int32_t *bucket, int tLen){
  freq = freq_8_32(text, freq, bucket, tLen);

  trim256(freq);
  trim256(bucket);

  int32_t total = 0;
  for (int i = 0; i < 256; i++) {
    bucket[i] = total;
    total += freq[i];
  }
}//end


/*func*/void bucketMax_8_32(byte *text, int32_t *freq, int32_t *bucket, int tLen){
  freq = freq_8_32(text, freq, bucket, tLen);

  trim256(freq);
  trim256(bucket);

  int32_t total = 0;
  for (int i = 0; i < 256; i++) {
    total += freq[i];
    bucket[i] = total;
  }
}//end

/*func*/int placeLMS_8_32(byte *text, int32_t *sa, int32_t *freq, int32_t *bucket, int tLen){
  bucketMax_8_32(text, freq, bucket, tLen);

  int numLMS = 0;
  int32_t lastB = -1;
  trim256(bucket);

  bool isTypeS = false;
  byte c0 = 0, c1 = 0;
  for (int i = tLen - 1; i >= 0; i--) {
    c1 = c0;
    c0 = text[i];

    if (c0 < c1) {
      isTypeS = true;
    } else if (c0 > c1 && isTypeS) {
      isTypeS = false;

      int32_t b = bucket[c1] - 1;
      bucket[c1] = b;
      sa[b] = (int32_t)(i+1);
      lastB = b;
      numLMS++;
    }
  }

  if (numLMS > 1) {
    sa[lastB] = 0;
  }

  return numLMS;
}//end


/*func*/void induceSubL_8_32(byte *text, int32_t *sa, int32_t *freq, int32_t *bucket, int tLen, int saLen){
  bucketMin_8_32(text, freq, bucket, tLen);
  trim256(bucket);

  int k = tLen-1;
  byte c0 = text[k-1];
  byte c1 = text[k];
  if (c0 < c1) k = -k;

  byte cB = c1;
  int32_t b = bucket[cB];
  sa[b] = (int32_t)k;
  b++;

  for (int i = 0; i < saLen; i++) {
    int j = sa[i];
    std::cout << j << std::endl;
    if (j == 0) continue;
    if (j < 0) {
      sa[i] = (int32_t)(-j);
      continue;
    }
    sa[i] = 0;

    int k = j - 1;
    byte c0 = text[k-1];
    byte c1 = text[k];
    if (c0 < c1) k = -k;
    if (cB != c1) {
      bucket[cB] = b;
      cB = c1;
      b = bucket[cB];
    }

    sa[b] = (int32_t)k;
    b++;
  }
}//end


/*func*/void induceSubS_8_32(byte *text, int32_t *sa, int32_t *freq, int32_t *bucket, int tLen, int saLen){
  bucketMax_8_32(text, freq, bucket, tLen);
  trim256(bucket);

  byte cB = 0;
  int32_t b = bucket[cB];

  int top = saLen;
  for (int i = saLen-1; i >= 0; i--) {
    int j = (int)sa[i];
    if (j == 0) continue;
    sa[i] = 0;
    if (j < 0) {
      top--;
      sa[top] = (int32_t)(-j);
      continue;
    }

    int k = j - 1;
    byte c0 = text[k-1];
    byte c1 = text[k];
    if (c0 > c1) k = -k;
    if (cB != c1) {
      bucket[cB] = b;
      cB = c1;
      b = bucket[cB];
    }
    b--;
    sa[b] = (int32_t)k;
  }
}//end


/*func*/void length_8_32(byte *text, int32_t *sa, int numLMS, int tLen){
  int end = 0;

  uint32_t cx = 0; // byte-only

  byte c0 = 0, c1 = 0;
  bool isTypeS = false;
  for (int i = tLen-1; i >= 0; i--) {
    c1 = c0;
    c0 = text[i];
    cx = cx<<8 | (uint32_t)(c1+1); // byte-only
    if (c0 < c1) {
      isTypeS = true;
    } else if (c0 > c1 && isTypeS) {
      isTypeS = false;

      int j = i + 1;
      int32_t code;
      if (end == 0) {
        code = 0;
      } else {
        code = (int32_t)(end-j);
        if (code <= 32/8 && ~(cx) >= (uint32_t)tLen) code = (int32_t)~(cx); // byte-only
      }
      sa[j>>1] = code;
      end = j + 1;
      cx = (uint32_t)(c1 + 1); // byte-only
    }
  }
}//end

/*func*/int assignID_8_32(byte *text, int32_t *sa, int textLen, int numLMS, int saLen){
  int id = 0;
  int32_t lastLen = -1;
  int32_t lastPos = 0;
  for (int i = saLen-numLMS; i < saLen; i++) {
    int32_t j = sa[i];
    int32_t n = sa[j/2];
    if (n != lastLen) goto New;
    if ((int32_t)n >= int32_t(textLen)) goto Same;
    {
      int n = (int)n;
      byte *current;
      byte *last;
      std::copy(text+j,text+n,current);
      std::copy(text+lastPos,text+n,current);
      for (int i = 0; i < (int)n; i++) {
        if (current[i] != last[i]) goto New;
      }
      goto Same;
    }
    New:
      id++;
      lastPos = j;
      lastPos = n;
    Same:
      sa[j/2] = (int32_t)id;
  }
  return id;
}//end

/*func*/void map_32(int32_t *sa, int numLMS, int saLen){
  int w = saLen;
  for (int i = saLen/2; i >= 0; i--) {
    int32_t j = sa[i];
    if (j > 0) {
      w--;
      sa[w] = j - 1;
    }
  }
}//end


/*func*/void recurse_32(int32_t *sa, int32_t *oldTmp, int numLMS, int maxID, int saLen, int tmpLen){
  int32_t dst[numLMS], saTmp[saLen-numLMS], text[saLen-numLMS];
  std::copy(sa, sa + numLMS, dst);
  std::copy(sa+numLMS, sa+saLen-numLMS, saTmp);
  std::copy(sa+saLen-numLMS, sa+saLen, text);

  int32_t *tmp = oldTmp;
  if (tmpLen < saLen-numLMS) {
    tmp = saTmp;
    tmpLen = saLen-numLMS;
  }
  if (tmpLen < numLMS) {
    int n = maxID;
    if (n < numLMS/2) n = numLMS/2;
    tmp = new int32_t[n];
    tmpLen = n;
  }

  for (int i = 0; i < numLMS; i++) dst[i] = 0;
  sais_32(text, maxID, dst, tmp, numLMS, saLen, tmpLen);
}//end


/*func*/void unmap_8_32(byte *text, int32_t *sa, int numLMS, int tLen, int saLen) {
  uint32_t unmap[saLen-numLMS];
  std::copy(sa + saLen - numLMS, sa + saLen, unmap);
  int j = numLMS;

  byte c0 = 0, c1 = 0;
  bool isTypeS = false;
  for (int i = tLen-1; i >= 0; i--) {
    c1 = c0;
    c0 = text[i];
    if (c0 < c1) {
      isTypeS = true;
    } else if (c0 > c1 && isTypeS) {
      isTypeS = false;

      j--;
      unmap[j] = (int32_t)(i+1);
    }
  }

  trimToSize(sa, numLMS);
  for (int i = 0; i < saLen; i++) {
    sa[i] = unmap[sa[i]];
  }
}//end


/*func*/void expand_8_32(byte *text, int32_t *freq, int32_t *bucket, int32_t *sa, int numLMS, int tLen, int saLen){
  bucketMax_8_32(text, freq, bucket, tLen);
  trim256(bucket);

  int x = numLMS - 1;
  int32_t saX = sa[x];
  byte c = text[saX];
  int32_t b;

  if (b < 256) {
    b = bucket[c] - 1;
    bucket[c] = b;
  }

  for (int i = saLen - 1; i >= 0; i--) {
    if (i != (int)b) {
      sa[i] = 0;
      continue;
    }
    sa[i] = saX;

    if (x > 0) {
      x--;
      saX = sa[x];
      c = text[saX];
      b = bucket[x]-1;
      if (c < 256) bucket[c] = b;
    }
  }
}//end


/*func*/void induceL_8_32(byte *text, int32_t *sa, int32_t *freq, int32_t *bucket, int tLen, int saLen) {
  bucketMin_8_32(text, freq, bucket, tLen);
  trim256(bucket);

  int k = tLen - 1;
  byte c0 = text[k-1];
  byte c1 = text[k];
  if (c0 < c1) k = -k;

  byte cB = c1;
  int32_t b = bucket[cB];
  sa[b] = (int32_t)k;
  b++;

  for (int i = 0; i < saLen; i++) {
    int j = (int)(sa[i]);
    if (j <= 0) continue;

    int k = j - 1;
    byte c1 = text[k];
    if (k > 0) {
      if (byte c0 = text[k-1]; c0 < c1) {
        k = -k;
      }
    }

    if (cB != c1) {
      bucket[cB] = b;
      cB = c1;
      b = bucket[cB];
    }
    sa[b] = (int32_t)(k);
    b++;
  }
}//end


/*func*/void induceS_8_32(byte *text, int32_t *sa, int32_t *freq, int32_t *bucket, int tLen, int saLen) {
  bucketMax_8_32(text, freq, bucket, tLen);
  trim256(bucket);

  byte cB = 0;
  int32_t b = bucket[cB];

  for (int i = saLen - 1; i >= 0; i--) {
    int j = (int)sa[i];
    if (j >= 0) continue;

    j = -j;
    sa[i] = (int32_t)j;

    int k = j - 1;
    byte c1 = text[k];
    if (k > 0) {
      if (byte c0 = text[k-1]; c0 <= c1) {
        k = -k;
      }
    }

    if (cB != c1) {
      bucket[cB] = b;
      cB = c1;
      b = bucket[cB];
    }
    b--;
    sa[b] = (int32_t)k;
  }
}//end
