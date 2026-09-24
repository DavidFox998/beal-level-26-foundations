import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1280
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1281
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1282
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1283
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1284
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1285
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1286
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1287
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1288
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1289

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_128 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 128 + i)) (500 * (10 * 128 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1280
  by_cases h1 : i = 1
  · subst i
    exact chunk_1281
  by_cases h2 : i = 2
  · subst i
    exact chunk_1282
  by_cases h3 : i = 3
  · subst i
    exact chunk_1283
  by_cases h4 : i = 4
  · subst i
    exact chunk_1284
  by_cases h5 : i = 5
  · subst i
    exact chunk_1285
  by_cases h6 : i = 6
  · subst i
    exact chunk_1286
  by_cases h7 : i = 7
  · subst i
    exact chunk_1287
  by_cases h8 : i = 8
  · subst i
    exact chunk_1288
  by_cases h9 : i = 9
  · subst i
    exact chunk_1289
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
