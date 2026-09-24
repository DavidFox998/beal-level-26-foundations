import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1250
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1251
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1252
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1253
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1254
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1255
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1256
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1257
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1258
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1259

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_125 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 125 + i)) (500 * (10 * 125 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1250
  by_cases h1 : i = 1
  · subst i
    exact chunk_1251
  by_cases h2 : i = 2
  · subst i
    exact chunk_1252
  by_cases h3 : i = 3
  · subst i
    exact chunk_1253
  by_cases h4 : i = 4
  · subst i
    exact chunk_1254
  by_cases h5 : i = 5
  · subst i
    exact chunk_1255
  by_cases h6 : i = 6
  · subst i
    exact chunk_1256
  by_cases h7 : i = 7
  · subst i
    exact chunk_1257
  by_cases h8 : i = 8
  · subst i
    exact chunk_1258
  by_cases h9 : i = 9
  · subst i
    exact chunk_1259
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
