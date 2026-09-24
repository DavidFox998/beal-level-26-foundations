import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1380
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1381
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1382
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1383
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1384
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1385
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1386
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1387
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1388
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1389

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_138 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 138 + i)) (500 * (10 * 138 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1380
  by_cases h1 : i = 1
  · subst i
    exact chunk_1381
  by_cases h2 : i = 2
  · subst i
    exact chunk_1382
  by_cases h3 : i = 3
  · subst i
    exact chunk_1383
  by_cases h4 : i = 4
  · subst i
    exact chunk_1384
  by_cases h5 : i = 5
  · subst i
    exact chunk_1385
  by_cases h6 : i = 6
  · subst i
    exact chunk_1386
  by_cases h7 : i = 7
  · subst i
    exact chunk_1387
  by_cases h8 : i = 8
  · subst i
    exact chunk_1388
  by_cases h9 : i = 9
  · subst i
    exact chunk_1389
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
