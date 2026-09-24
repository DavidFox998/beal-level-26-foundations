import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1470
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1471
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1472
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1473
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1474
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1475
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1476
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1477
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1478
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1479

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_147 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 147 + i)) (500 * (10 * 147 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1470
  by_cases h1 : i = 1
  · subst i
    exact chunk_1471
  by_cases h2 : i = 2
  · subst i
    exact chunk_1472
  by_cases h3 : i = 3
  · subst i
    exact chunk_1473
  by_cases h4 : i = 4
  · subst i
    exact chunk_1474
  by_cases h5 : i = 5
  · subst i
    exact chunk_1475
  by_cases h6 : i = 6
  · subst i
    exact chunk_1476
  by_cases h7 : i = 7
  · subst i
    exact chunk_1477
  by_cases h8 : i = 8
  · subst i
    exact chunk_1478
  by_cases h9 : i = 9
  · subst i
    exact chunk_1479
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
