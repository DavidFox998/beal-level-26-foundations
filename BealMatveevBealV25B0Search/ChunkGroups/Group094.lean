import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0940
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0941
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0942
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0943
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0944
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0945
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0946
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0947
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0948
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0949

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_094 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 94 + i)) (500 * (10 * 94 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0940
  by_cases h1 : i = 1
  · subst i
    exact chunk_0941
  by_cases h2 : i = 2
  · subst i
    exact chunk_0942
  by_cases h3 : i = 3
  · subst i
    exact chunk_0943
  by_cases h4 : i = 4
  · subst i
    exact chunk_0944
  by_cases h5 : i = 5
  · subst i
    exact chunk_0945
  by_cases h6 : i = 6
  · subst i
    exact chunk_0946
  by_cases h7 : i = 7
  · subst i
    exact chunk_0947
  by_cases h8 : i = 8
  · subst i
    exact chunk_0948
  by_cases h9 : i = 9
  · subst i
    exact chunk_0949
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
