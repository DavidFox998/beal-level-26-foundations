import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0470
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0471
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0472
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0473
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0474
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0475
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0476
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0477
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0478
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0479

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_047 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 47 + i)) (500 * (10 * 47 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0470
  by_cases h1 : i = 1
  · subst i
    exact chunk_0471
  by_cases h2 : i = 2
  · subst i
    exact chunk_0472
  by_cases h3 : i = 3
  · subst i
    exact chunk_0473
  by_cases h4 : i = 4
  · subst i
    exact chunk_0474
  by_cases h5 : i = 5
  · subst i
    exact chunk_0475
  by_cases h6 : i = 6
  · subst i
    exact chunk_0476
  by_cases h7 : i = 7
  · subst i
    exact chunk_0477
  by_cases h8 : i = 8
  · subst i
    exact chunk_0478
  by_cases h9 : i = 9
  · subst i
    exact chunk_0479
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
