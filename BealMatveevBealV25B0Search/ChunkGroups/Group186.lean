import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1860
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1861
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1862
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1863
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1864
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1865
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1866
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1867
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1868
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1869

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_186 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 186 + i)) (500 * (10 * 186 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1860
  by_cases h1 : i = 1
  · subst i
    exact chunk_1861
  by_cases h2 : i = 2
  · subst i
    exact chunk_1862
  by_cases h3 : i = 3
  · subst i
    exact chunk_1863
  by_cases h4 : i = 4
  · subst i
    exact chunk_1864
  by_cases h5 : i = 5
  · subst i
    exact chunk_1865
  by_cases h6 : i = 6
  · subst i
    exact chunk_1866
  by_cases h7 : i = 7
  · subst i
    exact chunk_1867
  by_cases h8 : i = 8
  · subst i
    exact chunk_1868
  by_cases h9 : i = 9
  · subst i
    exact chunk_1869
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
