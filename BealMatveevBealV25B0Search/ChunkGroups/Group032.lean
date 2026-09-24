import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0320
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0321
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0322
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0323
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0324
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0325
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0326
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0327
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0328
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0329

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_032 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 32 + i)) (500 * (10 * 32 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0320
  by_cases h1 : i = 1
  · subst i
    exact chunk_0321
  by_cases h2 : i = 2
  · subst i
    exact chunk_0322
  by_cases h3 : i = 3
  · subst i
    exact chunk_0323
  by_cases h4 : i = 4
  · subst i
    exact chunk_0324
  by_cases h5 : i = 5
  · subst i
    exact chunk_0325
  by_cases h6 : i = 6
  · subst i
    exact chunk_0326
  by_cases h7 : i = 7
  · subst i
    exact chunk_0327
  by_cases h8 : i = 8
  · subst i
    exact chunk_0328
  by_cases h9 : i = 9
  · subst i
    exact chunk_0329
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
