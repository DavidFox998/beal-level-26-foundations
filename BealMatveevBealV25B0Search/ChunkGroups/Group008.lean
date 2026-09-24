import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0080
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0081
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0082
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0083
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0084
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0085
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0086
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0087
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0088
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0089

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_008 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 8 + i)) (500 * (10 * 8 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0080
  by_cases h1 : i = 1
  · subst i
    exact chunk_0081
  by_cases h2 : i = 2
  · subst i
    exact chunk_0082
  by_cases h3 : i = 3
  · subst i
    exact chunk_0083
  by_cases h4 : i = 4
  · subst i
    exact chunk_0084
  by_cases h5 : i = 5
  · subst i
    exact chunk_0085
  by_cases h6 : i = 6
  · subst i
    exact chunk_0086
  by_cases h7 : i = 7
  · subst i
    exact chunk_0087
  by_cases h8 : i = 8
  · subst i
    exact chunk_0088
  by_cases h9 : i = 9
  · subst i
    exact chunk_0089
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
