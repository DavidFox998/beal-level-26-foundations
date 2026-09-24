import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0040
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0041
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0042
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0043
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0044
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0045
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0046
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0047
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0048
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0049

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_004 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 4 + i)) (500 * (10 * 4 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0040
  by_cases h1 : i = 1
  · subst i
    exact chunk_0041
  by_cases h2 : i = 2
  · subst i
    exact chunk_0042
  by_cases h3 : i = 3
  · subst i
    exact chunk_0043
  by_cases h4 : i = 4
  · subst i
    exact chunk_0044
  by_cases h5 : i = 5
  · subst i
    exact chunk_0045
  by_cases h6 : i = 6
  · subst i
    exact chunk_0046
  by_cases h7 : i = 7
  · subst i
    exact chunk_0047
  by_cases h8 : i = 8
  · subst i
    exact chunk_0048
  by_cases h9 : i = 9
  · subst i
    exact chunk_0049
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
