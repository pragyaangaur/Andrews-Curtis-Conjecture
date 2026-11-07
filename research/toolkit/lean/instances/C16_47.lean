import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 47 of the cap-16 certificate: slots 48128 .. 49151 -/
theorem chk_47 : chunkCheck 16 T stdSt 48128 1024 = true := by decide +kernel

end Row16
