import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1420
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1421
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1422
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1423
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1424
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1425
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1426
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1427
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1428
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1429

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_142 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 142 + i)) (500 * (10 * 142 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1420
  by_cases h1 : i = 1
  · subst i
    exact chunk_1421
  by_cases h2 : i = 2
  · subst i
    exact chunk_1422
  by_cases h3 : i = 3
  · subst i
    exact chunk_1423
  by_cases h4 : i = 4
  · subst i
    exact chunk_1424
  by_cases h5 : i = 5
  · subst i
    exact chunk_1425
  by_cases h6 : i = 6
  · subst i
    exact chunk_1426
  by_cases h7 : i = 7
  · subst i
    exact chunk_1427
  by_cases h8 : i = 8
  · subst i
    exact chunk_1428
  by_cases h9 : i = 9
  · subst i
    exact chunk_1429
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
