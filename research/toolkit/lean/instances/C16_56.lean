import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 56 of the cap-16 certificate: slots 57344 .. 58367 -/
theorem chk_56 : chunkCheck 16 T stdSt 57344 1024 = true := by decide +kernel

end Row16
