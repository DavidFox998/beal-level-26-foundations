import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0890
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0891
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0892
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0893
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0894
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0895
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0896
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0897
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0898
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0899

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_089 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 89 + i)) (500 * (10 * 89 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0890
  by_cases h1 : i = 1
  · subst i
    exact chunk_0891
  by_cases h2 : i = 2
  · subst i
    exact chunk_0892
  by_cases h3 : i = 3
  · subst i
    exact chunk_0893
  by_cases h4 : i = 4
  · subst i
    exact chunk_0894
  by_cases h5 : i = 5
  · subst i
    exact chunk_0895
  by_cases h6 : i = 6
  · subst i
    exact chunk_0896
  by_cases h7 : i = 7
  · subst i
    exact chunk_0897
  by_cases h8 : i = 8
  · subst i
    exact chunk_0898
  by_cases h9 : i = 9
  · subst i
    exact chunk_0899
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
