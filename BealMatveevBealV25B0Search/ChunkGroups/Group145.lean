import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1450
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1451
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1452
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1453
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1454
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1455
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1456
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1457
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1458
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1459

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_145 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 145 + i)) (500 * (10 * 145 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1450
  by_cases h1 : i = 1
  · subst i
    exact chunk_1451
  by_cases h2 : i = 2
  · subst i
    exact chunk_1452
  by_cases h3 : i = 3
  · subst i
    exact chunk_1453
  by_cases h4 : i = 4
  · subst i
    exact chunk_1454
  by_cases h5 : i = 5
  · subst i
    exact chunk_1455
  by_cases h6 : i = 6
  · subst i
    exact chunk_1456
  by_cases h7 : i = 7
  · subst i
    exact chunk_1457
  by_cases h8 : i = 8
  · subst i
    exact chunk_1458
  by_cases h9 : i = 9
  · subst i
    exact chunk_1459
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
