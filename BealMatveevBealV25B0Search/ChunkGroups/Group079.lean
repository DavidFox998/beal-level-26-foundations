import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0790
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0791
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0792
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0793
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0794
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0795
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0796
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0797
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0798
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0799

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_079 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 79 + i)) (500 * (10 * 79 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0790
  by_cases h1 : i = 1
  · subst i
    exact chunk_0791
  by_cases h2 : i = 2
  · subst i
    exact chunk_0792
  by_cases h3 : i = 3
  · subst i
    exact chunk_0793
  by_cases h4 : i = 4
  · subst i
    exact chunk_0794
  by_cases h5 : i = 5
  · subst i
    exact chunk_0795
  by_cases h6 : i = 6
  · subst i
    exact chunk_0796
  by_cases h7 : i = 7
  · subst i
    exact chunk_0797
  by_cases h8 : i = 8
  · subst i
    exact chunk_0798
  by_cases h9 : i = 9
  · subst i
    exact chunk_0799
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
