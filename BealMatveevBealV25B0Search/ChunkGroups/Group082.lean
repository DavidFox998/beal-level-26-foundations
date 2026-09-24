import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0820
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0821
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0822
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0823
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0824
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0825
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0826
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0827
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0828
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0829

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_082 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 82 + i)) (500 * (10 * 82 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0820
  by_cases h1 : i = 1
  · subst i
    exact chunk_0821
  by_cases h2 : i = 2
  · subst i
    exact chunk_0822
  by_cases h3 : i = 3
  · subst i
    exact chunk_0823
  by_cases h4 : i = 4
  · subst i
    exact chunk_0824
  by_cases h5 : i = 5
  · subst i
    exact chunk_0825
  by_cases h6 : i = 6
  · subst i
    exact chunk_0826
  by_cases h7 : i = 7
  · subst i
    exact chunk_0827
  by_cases h8 : i = 8
  · subst i
    exact chunk_0828
  by_cases h9 : i = 9
  · subst i
    exact chunk_0829
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
