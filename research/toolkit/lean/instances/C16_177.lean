import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 177 of the cap-16 certificate: slots 181248 .. 182271 -/
theorem chk_177 : chunkCheck 16 T stdSt 181248 1024 = true := by decide +kernel

end Row16
