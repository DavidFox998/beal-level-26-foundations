import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0680
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0681
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0682
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0683
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0684
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0685
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0686
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0687
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0688
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0689

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_068 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 68 + i)) (500 * (10 * 68 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0680
  by_cases h1 : i = 1
  · subst i
    exact chunk_0681
  by_cases h2 : i = 2
  · subst i
    exact chunk_0682
  by_cases h3 : i = 3
  · subst i
    exact chunk_0683
  by_cases h4 : i = 4
  · subst i
    exact chunk_0684
  by_cases h5 : i = 5
  · subst i
    exact chunk_0685
  by_cases h6 : i = 6
  · subst i
    exact chunk_0686
  by_cases h7 : i = 7
  · subst i
    exact chunk_0687
  by_cases h8 : i = 8
  · subst i
    exact chunk_0688
  by_cases h9 : i = 9
  · subst i
    exact chunk_0689
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
