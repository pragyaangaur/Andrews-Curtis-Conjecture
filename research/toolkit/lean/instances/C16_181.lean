import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 181 of the cap-16 certificate: slots 185344 .. 186367 -/
theorem chk_181 : chunkCheck 16 T stdSt 185344 1024 = true := by decide +kernel

end Row16
