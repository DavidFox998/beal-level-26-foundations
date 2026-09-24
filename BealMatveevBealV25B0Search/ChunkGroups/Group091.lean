import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0910
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0911
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0912
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0913
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0914
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0915
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0916
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0917
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0918
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0919

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_091 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 91 + i)) (500 * (10 * 91 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0910
  by_cases h1 : i = 1
  · subst i
    exact chunk_0911
  by_cases h2 : i = 2
  · subst i
    exact chunk_0912
  by_cases h3 : i = 3
  · subst i
    exact chunk_0913
  by_cases h4 : i = 4
  · subst i
    exact chunk_0914
  by_cases h5 : i = 5
  · subst i
    exact chunk_0915
  by_cases h6 : i = 6
  · subst i
    exact chunk_0916
  by_cases h7 : i = 7
  · subst i
    exact chunk_0917
  by_cases h8 : i = 8
  · subst i
    exact chunk_0918
  by_cases h9 : i = 9
  · subst i
    exact chunk_0919
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
