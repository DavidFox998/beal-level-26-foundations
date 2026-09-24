import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0620
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0621
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0622
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0623
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0624
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0625
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0626
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0627
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0628
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0629

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_062 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 62 + i)) (500 * (10 * 62 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0620
  by_cases h1 : i = 1
  · subst i
    exact chunk_0621
  by_cases h2 : i = 2
  · subst i
    exact chunk_0622
  by_cases h3 : i = 3
  · subst i
    exact chunk_0623
  by_cases h4 : i = 4
  · subst i
    exact chunk_0624
  by_cases h5 : i = 5
  · subst i
    exact chunk_0625
  by_cases h6 : i = 6
  · subst i
    exact chunk_0626
  by_cases h7 : i = 7
  · subst i
    exact chunk_0627
  by_cases h8 : i = 8
  · subst i
    exact chunk_0628
  by_cases h9 : i = 9
  · subst i
    exact chunk_0629
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
