import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0860
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0861
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0862
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0863
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0864
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0865
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0866
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0867
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0868
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0869

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_086 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 86 + i)) (500 * (10 * 86 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0860
  by_cases h1 : i = 1
  · subst i
    exact chunk_0861
  by_cases h2 : i = 2
  · subst i
    exact chunk_0862
  by_cases h3 : i = 3
  · subst i
    exact chunk_0863
  by_cases h4 : i = 4
  · subst i
    exact chunk_0864
  by_cases h5 : i = 5
  · subst i
    exact chunk_0865
  by_cases h6 : i = 6
  · subst i
    exact chunk_0866
  by_cases h7 : i = 7
  · subst i
    exact chunk_0867
  by_cases h8 : i = 8
  · subst i
    exact chunk_0868
  by_cases h9 : i = 9
  · subst i
    exact chunk_0869
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
