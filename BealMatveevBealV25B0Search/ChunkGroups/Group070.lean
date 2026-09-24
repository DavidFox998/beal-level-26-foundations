import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0700
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0701
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0702
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0703
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0704
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0705
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0706
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0707
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0708
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0709

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_070 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 70 + i)) (500 * (10 * 70 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0700
  by_cases h1 : i = 1
  · subst i
    exact chunk_0701
  by_cases h2 : i = 2
  · subst i
    exact chunk_0702
  by_cases h3 : i = 3
  · subst i
    exact chunk_0703
  by_cases h4 : i = 4
  · subst i
    exact chunk_0704
  by_cases h5 : i = 5
  · subst i
    exact chunk_0705
  by_cases h6 : i = 6
  · subst i
    exact chunk_0706
  by_cases h7 : i = 7
  · subst i
    exact chunk_0707
  by_cases h8 : i = 8
  · subst i
    exact chunk_0708
  by_cases h9 : i = 9
  · subst i
    exact chunk_0709
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
