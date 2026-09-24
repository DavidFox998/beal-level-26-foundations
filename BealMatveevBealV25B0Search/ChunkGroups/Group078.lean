import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0780
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0781
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0782
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0783
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0784
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0785
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0786
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0787
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0788
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0789

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_078 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 78 + i)) (500 * (10 * 78 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0780
  by_cases h1 : i = 1
  · subst i
    exact chunk_0781
  by_cases h2 : i = 2
  · subst i
    exact chunk_0782
  by_cases h3 : i = 3
  · subst i
    exact chunk_0783
  by_cases h4 : i = 4
  · subst i
    exact chunk_0784
  by_cases h5 : i = 5
  · subst i
    exact chunk_0785
  by_cases h6 : i = 6
  · subst i
    exact chunk_0786
  by_cases h7 : i = 7
  · subst i
    exact chunk_0787
  by_cases h8 : i = 8
  · subst i
    exact chunk_0788
  by_cases h9 : i = 9
  · subst i
    exact chunk_0789
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
