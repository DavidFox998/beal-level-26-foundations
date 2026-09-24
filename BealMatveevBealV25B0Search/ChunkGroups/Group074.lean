import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0740
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0741
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0742
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0743
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0744
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0745
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0746
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0747
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0748
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0749

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_074 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 74 + i)) (500 * (10 * 74 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0740
  by_cases h1 : i = 1
  · subst i
    exact chunk_0741
  by_cases h2 : i = 2
  · subst i
    exact chunk_0742
  by_cases h3 : i = 3
  · subst i
    exact chunk_0743
  by_cases h4 : i = 4
  · subst i
    exact chunk_0744
  by_cases h5 : i = 5
  · subst i
    exact chunk_0745
  by_cases h6 : i = 6
  · subst i
    exact chunk_0746
  by_cases h7 : i = 7
  · subst i
    exact chunk_0747
  by_cases h8 : i = 8
  · subst i
    exact chunk_0748
  by_cases h9 : i = 9
  · subst i
    exact chunk_0749
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
