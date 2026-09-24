import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0930
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0931
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0932
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0933
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0934
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0935
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0936
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0937
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0938
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0939

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_093 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 93 + i)) (500 * (10 * 93 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0930
  by_cases h1 : i = 1
  · subst i
    exact chunk_0931
  by_cases h2 : i = 2
  · subst i
    exact chunk_0932
  by_cases h3 : i = 3
  · subst i
    exact chunk_0933
  by_cases h4 : i = 4
  · subst i
    exact chunk_0934
  by_cases h5 : i = 5
  · subst i
    exact chunk_0935
  by_cases h6 : i = 6
  · subst i
    exact chunk_0936
  by_cases h7 : i = 7
  · subst i
    exact chunk_0937
  by_cases h8 : i = 8
  · subst i
    exact chunk_0938
  by_cases h9 : i = 9
  · subst i
    exact chunk_0939
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
