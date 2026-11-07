import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 89 of the cap-16 certificate: slots 91136 .. 92159 -/
theorem chk_89 : chunkCheck 16 T stdSt 91136 1024 = true := by decide +kernel

end Row16
