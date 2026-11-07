import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 203 of the cap-17 certificate: slots 103936 .. 104447 -/
theorem chk_203 : chunkCheck 17 T stdSt 103936 512 = true := by decide +kernel

end Row17
