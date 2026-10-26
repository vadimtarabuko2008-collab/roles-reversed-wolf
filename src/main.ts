import * as THREE from 'three';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';
import { clone as cloneSkeleton } from 'three/addons/utils/SkeletonUtils.js';
import './style.css';

type Phase = 'День' | 'Сумерки' | 'Ночь' | 'Рассвет';
type SheepState = 'graze' | 'wander' | 'flee' | 'carried';
type DogState = 'patrol' | 'alert' | 'chase' | 'search-visual' | 'search-scent' | 'return';
type RivalState = 'hidden' | 'approach' | 'carry' | 'fight' | 'retreat' | 'escape-warning';
type ShepherdState = 'resting' | 'patrol' | 'investigate' | 'aim' | 'reload';

interface Sheep {
  id: number;
  mesh: THREE.Group;
  velocity: THREE.Vector3;
  alive: boolean;
  turnIn: number;
  state: SheepState;
  carriedBy: 'player' | 'rival' | null;
  bobOffset: number;
  bell: boolean;
  panicMemory: number;
}

interface ScentMark {
  position: THREE.Vector3;
  age: number;
  strength: number;
}

interface Obstacle {
  position: THREE.Vector3;
  radius: number;
}

interface Rival {
  mesh: THREE.Group;
  velocity: THREE.Vector3;
  state: RivalState;
  hp: number;
  target?: Sheep;
  carrying?: Sheep;
  exit: THREE.Vector3;
  exitTimer: number;
  attackCooldown: number;
  attackWindup: number;
}

interface AnimatedRig {
  mixer: THREE.AnimationMixer;
  actions: Map<string, THREE.AnimationAction>;
  current?: THREE.AnimationAction;
  currentName?: string;
}

interface AmbientAnimal {
  mesh: THREE.Group;
  velocity: THREE.Vector3;
  wanderDirection: THREE.Vector3;
  turnIn: number;
}

const MAP_W = 32;
const MAP_H = 24;
const GOAL = 4;
const START_HEALTH = 6;
const CHANGE_TIME = 3;
const CYCLE_TIME = 120;
const DASH_COOLDOWN = 5;

const ui = {
  phase: required('phase'),
  day: required('day'),
  time: required('time'),
  sheep: required('sheep'),
  lost: required('lost'),
  health: required('health'),
  form: required('form'),
  costume: required('costume'),
  carrying: required('carrying'),
  danger: required('danger'),
  rival: required('rival-status'),
  dash: required('dash-status'),
  models: required('models-status'),
  hint: required('hint'),
  progress: required('change-progress'),
  sound: requiredButton('sound'),
  overlay: required('overlay'),
  overlayTitle: required('overlay-title'),
  overlayText: required('overlay-text'),
  start: requiredButton('start'),
};

function required(id: string): HTMLElement {
  const element = document.getElementById(id);
  if (!element) throw new Error(`Missing element #${id}`);
  return element;
}

function requiredButton(id: string): HTMLButtonElement {
  const element = required(id);
  if (!(element instanceof HTMLButtonElement)) throw new Error(`#${id} is not a button`);
  return element;
}

class PrototypeGame {
  private readonly scene = new THREE.Scene();
  private readonly camera: THREE.PerspectiveCamera;
  private readonly renderer = new THREE.WebGLRenderer({ antialias: true });
  private readonly loader = new GLTFLoader();
  private readonly clock = new THREE.Clock();
  private readonly keys = new Set<string>();
  private readonly pressed = new Set<string>();
  private readonly sheep: Sheep[] = [];
  private readonly scents: ScentMark[] = [];
  private readonly obstacles: Obstacle[] = [];
  private readonly wolf = this.createWolf();
  private readonly dog = this.createDog();
  private readonly rival: Rival = {
    mesh: this.createRival(),
    velocity: new THREE.Vector3(),
    state: 'hidden',
    hp: 3,
    exit: new THREE.Vector3(-15, 0, 0),
    exitTimer: 0,
    attackCooldown: 0,
    attackWindup: 0,
  };
  private readonly shepherd = this.createShepherd();
  private readonly sun = new THREE.DirectionalLight(0xffedc7, 2.1);
  private readonly sky = new THREE.HemisphereLight(0xc7e9ff, 0x344223, 1.6);
  private readonly lanterns: THREE.PointLight[] = [];
  private readonly cameraTarget = new THREE.Vector3();
  private readonly rigs = new Map<THREE.Object3D, AnimatedRig>();
  private readonly ambientAnimals: AmbientAnimal[] = [];
  private readonly playerVelocity = new THREE.Vector3();
  private readonly dashDirection = new THREE.Vector3(1, 0, 0);
  private readonly dogVelocity = new THREE.Vector3();
  private readonly dogFacing = new THREE.Vector3(1, 0, 0);
  private readonly dogLastSeen = new THREE.Vector3();
  private readonly dogPatrolPoints = [
    new THREE.Vector3(-10, 0, -7),
    new THREE.Vector3(0, 0, -7),
    new THREE.Vector3(9, 0, -3),
    new THREE.Vector3(8, 0, 7),
    new THREE.Vector3(-7, 0, 7),
    new THREE.Vector3(-11, 0, 0),
  ];
  private readonly shepherdPatrolPoints = [
    new THREE.Vector3(7.5, 0, -5.2),
    new THREE.Vector3(5, 0, -3),
    new THREE.Vector3(8, 0, 5),
  ];

  private running = false;
  private finished = false;
  private disguised = true;
  private elapsed = 0;
  private changeProgress = 0;
  private score = 0;
  private health = START_HEALTH;
  private maxHealth = START_HEALTH;
  private biteCooldown = 0;
  private actionCooldown = 0;
  private phase: Phase = 'День';
  private previousPhase: Phase = 'День';
  private dayNumber = 1;
  private cycleIndex = 0;
  private guardLevel = 0;
  private lostSheep = 0;
  private perfectPossible = true;
  private victoryPending = false;
  private playerCarrying?: Sheep;
  private eatProgress = 0;
  private repairProgress = 0;
  private costumeIntegrity = 2;
  private repairKits = 2;
  private bleatCooldown = 0;
  private lureTime = 0;
  private luredSheep?: Sheep;
  private readonly bleatTimes: number[] = [];
  private bellNoiseCooldown = 0;
  private isGrazing = false;
  private playerHeld = 0;
  private playerHeldElapsed = 0;
  private dashCooldown = 0;
  private dashTime = 0;
  private scentTimer = 0;
  private disguiseScentTail = 0;
  private dogState: DogState = 'patrol';
  private dogSuspicion = 0;
  private dogSearchTime = 0;
  private dogBiteWindup = 0;
  private dogConfirmed = false;
  private dogRivalCommit = 0;
  private dogPatrolIndex = 0;
  private shepherdState: ShepherdState = 'resting';
  private shepherdPatrolIndex = 0;
  private shepherdAim = 0;
  private shepherdReload = 0;
  private rivalEntriesThisNight = 0;
  private nextRivalSpawn = 66;
  private dashHitRival = false;
  private paused = false;
  private audioContext?: AudioContext;
  private soundEnabled = true;
  private feedbackMessage = '';
  private feedbackTime = 0;
  private modelStatus = 'Загрузка временных 3D-моделей…';
  private cameraYaw = Math.PI * .25;
  private cameraPitch = THREE.MathUtils.degToRad(49);
  private cameraDistance = 25;
  private cameraDragging = false;
  private cameraPointerX = 0;
  private cameraPointerY = 0;

  constructor(container: HTMLElement) {
    try {
      this.soundEnabled = localStorage.getItem('roles-reversed-wolf.sound') !== 'off';
    } catch {
      this.soundEnabled = true;
    }
    ui.sound.textContent = `Звук: ${this.soundEnabled ? 'вкл' : 'выкл'}`;
    ui.sound.setAttribute('aria-pressed', String(this.soundEnabled));
    const aspect = window.innerWidth / window.innerHeight;
    this.camera = new THREE.PerspectiveCamera(42, aspect, .1, 120);
    this.camera.position.set(18, 20, 18);
    this.camera.lookAt(0, 0, 0);

    this.renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5));
    this.renderer.setSize(window.innerWidth, window.innerHeight);
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    container.appendChild(this.renderer.domElement);

    this.buildWorld();
    this.bindEvents();
    void this.loadModels();
    this.reset();
    this.renderer.setAnimationLoop(() => this.frame());
  }

  start(): void {
    this.ensureAudio();
    this.playTone(392, .1, .05);
    window.setTimeout(() => this.playTone(523, .13, .04), 90);
    this.reset();
    this.running = true;
    this.paused = false;
    ui.overlay.classList.add('hidden');
    this.clock.start();
  }

  private reset(): void {
    this.keys.clear();
    this.pressed.clear();
    this.finished = false;
    this.running = false;
    this.elapsed = 0;
    this.score = 0;
    this.health = START_HEALTH;
    this.maxHealth = START_HEALTH;
    this.disguised = true;
    this.changeProgress = 0;
    this.biteCooldown = 0;
    this.actionCooldown = 0;
    this.dayNumber = 1;
    this.cycleIndex = 0;
    this.guardLevel = 0;
    this.lostSheep = 0;
    this.perfectPossible = true;
    this.victoryPending = false;
    this.playerCarrying = undefined;
    this.eatProgress = 0;
    this.repairProgress = 0;
    this.costumeIntegrity = 2;
    this.repairKits = 2;
    this.bleatCooldown = 0;
    this.lureTime = 0;
    this.luredSheep = undefined;
    this.bleatTimes.length = 0;
    this.bellNoiseCooldown = 0;
    this.isGrazing = false;
    this.playerHeld = 0;
    this.playerHeldElapsed = 0;
    this.dashCooldown = 0;
    this.dashTime = 0;
    this.dashDirection.set(1, 0, 0);
    this.scentTimer = 0;
    this.disguiseScentTail = 0;
    this.scents.length = 0;
    this.playerVelocity.set(0, 0, 0);
    this.wolf.position.set(0, 0, 5);
    this.dog.position.set(-10, 0, -7);
    this.dogVelocity.set(0, 0, 0);
    this.dogFacing.set(1, 0, 0);
    this.dogState = 'patrol';
    this.dogSuspicion = 0;
    this.dogSearchTime = 0;
    this.dogBiteWindup = 0;
    this.dogConfirmed = false;
    this.dogRivalCommit = 0;
    this.dogPatrolIndex = 0;
    this.rival.state = 'hidden';
    this.rival.mesh.visible = false;
    this.rival.hp = 3;
    this.rival.target = undefined;
    this.rival.carrying = undefined;
    this.rival.velocity.set(0, 0, 0);
    this.rival.exitTimer = 0;
    this.rival.attackWindup = 0;
    this.shepherdState = 'resting';
    this.shepherd.visible = false;
    this.shepherd.position.set(11, 0, -8);
    this.shepherdAim = 0;
    this.shepherdReload = 0;
    this.rivalEntriesThisNight = 0;
    this.nextRivalSpawn = 66;
    this.dashHitRival = false;
    this.paused = false;
    this.feedbackMessage = '';
    this.feedbackTime = 0;
    this.previousPhase = 'День';
    this.phase = 'День';
    this.setDisguiseVisual();
    this.resetSheep();
    this.updateUi();
  }

  private buildWorld(): void {
    this.scene.background = new THREE.Color(0xaacb8b);
    this.scene.fog = new THREE.Fog(0xaacb8b, 25, 52);

    const ground = new THREE.Mesh(
      new THREE.PlaneGeometry(MAP_W, MAP_H),
      new THREE.MeshStandardMaterial({ color: 0x64814e, roughness: 1 }),
    );
    ground.rotation.x = -Math.PI / 2;
    ground.receiveShadow = true;
    this.scene.add(ground);

    this.sun.position.set(10, 20, 8);
    this.sun.castShadow = true;
    this.sun.shadow.mapSize.set(1024, 1024);
    this.scene.add(this.sun, this.sky);

    const lanternMaterial = new THREE.MeshStandardMaterial({
      color: 0xffc36a,
      emissive: 0xff8a2b,
      emissiveIntensity: 1.8,
      roughness: .45,
    });
    for (const [x, z] of [[-13, -9], [10, -8], [-12, 8], [11, 8], [0, -10]] as const) {
      const post = new THREE.Mesh(
        new THREE.CylinderGeometry(.07, .09, 1.7, 7),
        new THREE.MeshStandardMaterial({ color: 0x4d3422, roughness: 1 }),
      );
      post.position.set(x, .85, z);
      const glow = new THREE.Mesh(new THREE.SphereGeometry(.13, 9, 7), lanternMaterial);
      glow.position.set(x, 1.72, z);
      const light = new THREE.PointLight(0xffa34d, .35, 9, 1.7);
      light.position.set(x, 1.7, z);
      light.castShadow = false;
      this.lanterns.push(light);
      this.scene.add(post, glow, light);
    }

    this.scene.add(this.wolf, this.dog, this.rival.mesh, this.shepherd);
    for (let i = 0; i < 8; i += 1) {
      const sheep: Sheep = {
        id: i,
        mesh: this.createSheep(i === 0),
        velocity: new THREE.Vector3(),
        alive: true,
        turnIn: 0,
        state: 'graze',
        carriedBy: null,
        bobOffset: random(0, Math.PI * 2),
        bell: i === 0,
        panicMemory: 0,
      };
      this.sheep.push(sheep);
      this.scene.add(sheep.mesh);
    }

    const fenceMaterial = new THREE.MeshStandardMaterial({ color: 0x765333, roughness: 1 });
    const addFence = (x: number, z: number, sx: number, sz: number) => {
      const fence = new THREE.Mesh(new THREE.BoxGeometry(sx, 0.8, sz), fenceMaterial);
      fence.position.set(x, 0.4, z);
      fence.castShadow = true;
      this.scene.add(fence);
    };
    addFence(0, -MAP_H / 2, MAP_W + 1, 0.28);
    addFence(0, MAP_H / 2, MAP_W + 1, 0.28);
    addFence(-MAP_W / 2, 0, 0.28, MAP_H + 1);
    addFence(MAP_W / 2, 0, 0.28, MAP_H + 1);

    const barn = new THREE.Mesh(
      new THREE.BoxGeometry(5, 3.5, 4),
      new THREE.MeshStandardMaterial({ color: 0x763f32, roughness: .9 }),
    );
    barn.position.set(11, 1.75, -8);
    barn.castShadow = true;
    barn.receiveShadow = true;
    this.scene.add(barn);
    this.obstacles.push({ position: new THREE.Vector3(11, 0, -8), radius: 3.15 });

    const rockMaterial = new THREE.MeshStandardMaterial({ color: 0x657064, roughness: 1 });
    for (const [x, z, radius] of [[-6, -3, 1.25], [4, 5, 1.1], [-9, 7, .9]] as const) {
      const rock = new THREE.Mesh(new THREE.DodecahedronGeometry(radius, 0), rockMaterial);
      rock.position.set(x, radius * .62, z);
      rock.scale.y = .75;
      rock.castShadow = true;
      this.scene.add(rock);
      this.obstacles.push({ position: new THREE.Vector3(x, 0, z), radius: radius + .35 });
    }

    for (let i = 0; i < 34; i += 1) {
      const tuft = new THREE.Mesh(
        new THREE.ConeGeometry(.08 + Math.random() * .08, .35 + Math.random() * .3, 4),
        new THREE.MeshStandardMaterial({ color: i % 3 === 0 ? 0x8ba964 : 0x759653 }),
      );
      tuft.position.set(random(-15, 15), .2, random(-11, 11));
      this.scene.add(tuft);
    }
  }

  private async loadModels(): Promise<void> {
    try {
      const [wolfAsset, huskyAsset, foxAsset, sheepAsset, donkeyAsset, cowAsset, farmAsset] = await Promise.all([
        this.loader.loadAsync('/assets/models/wolf.gltf'),
        this.loader.loadAsync('/assets/models/husky.gltf'),
        this.loader.loadAsync('/assets/models/fox.gltf'),
        this.loader.loadAsync('/assets/models/sheep-placeholder.gltf'),
        this.loader.loadAsync('/assets/models/donkey.gltf'),
        this.loader.loadAsync('/assets/models/cow.gltf'),
        this.loader.loadAsync('/assets/models/farmyard.glb'),
      ]);

      this.installRig(this.wolf, wolfAsset.scene, wolfAsset.animations, 1.55, Math.PI / 2, ['coat']);
      this.installRig(this.dog, huskyAsset.scene, huskyAsset.animations, 1.35, Math.PI / 2, ['attention']);
      this.installRig(this.rival.mesh, foxAsset.scene, foxAsset.animations, 1.3, Math.PI / 2, ['attack-warning']);
      for (const sheep of this.sheep) {
        this.installRig(
          sheep.mesh,
          sheepAsset.scene,
          sheepAsset.animations,
          1.12,
          Math.PI / 2,
          sheep.bell ? ['bell'] : [],
        );
      }

      const ambientSpecs = [
        { source: donkeyAsset.scene, clips: donkeyAsset.animations, height: 1.55, position: new THREE.Vector3(-12, 0, -8) },
        { source: cowAsset.scene, clips: cowAsset.animations, height: 1.65, position: new THREE.Vector3(11, 0, 7) },
      ];
      for (const spec of ambientSpecs) {
        const mesh = new THREE.Group();
        mesh.position.copy(spec.position);
        this.scene.add(mesh);
        this.installRig(mesh, spec.source, spec.clips, spec.height, Math.PI / 2, []);
        const angle = random(0, Math.PI * 2);
        this.ambientAnimals.push({
          mesh,
          velocity: new THREE.Vector3(),
          wanderDirection: new THREE.Vector3(Math.cos(angle), 0, Math.sin(angle)),
          turnIn: random(2, 5),
        });
      }

      const farmyard = cloneSkeleton(farmAsset.scene);
      farmyard.name = 'farmyard-backdrop';
      farmyard.scale.setScalar(1.05);
      farmyard.position.set(-1.5, 0, -17);
      farmyard.rotation.y = -.06;
      farmyard.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.castShadow = true;
          child.receiveShadow = true;
        }
      });
      this.scene.add(farmyard);
      this.modelStatus = 'Модели: Wolf · Husky · Fox · Alpaca · Donkey · Cow';
    } catch (error) {
      console.error('Не удалось загрузить временные модели', error);
      this.modelStatus = 'Модели: процедурный резерв (ошибка загрузки)';
    }
    this.updateUi();
  }

  private installRig(
    actor: THREE.Group,
    source: THREE.Object3D,
    clips: THREE.AnimationClip[],
    targetHeight: number,
    rotationY: number,
    keepNames: string[],
  ): void {
    const model = cloneSkeleton(source);
    model.name = 'animated-model';
    model.rotation.y = rotationY;
    model.updateMatrixWorld(true);
    const initialBox = new THREE.Box3().setFromObject(model);
    const initialHeight = Math.max(.001, initialBox.max.y - initialBox.min.y);
    model.scale.setScalar(targetHeight / initialHeight);
    model.updateMatrixWorld(true);
    const box = new THREE.Box3().setFromObject(model);
    const center = box.getCenter(new THREE.Vector3());
    model.position.set(-center.x, -box.min.y, -center.z);
    model.traverse((child) => {
      if (child instanceof THREE.Mesh) {
        child.castShadow = true;
        child.receiveShadow = true;
        child.frustumCulled = false;
      }
    });

    for (const child of actor.children) {
      if (!keepNames.includes(child.name)) child.visible = false;
    }
    actor.add(model);

    const mixer = new THREE.AnimationMixer(model);
    const actions = new Map<string, THREE.AnimationAction>();
    for (const clip of clips) actions.set(clip.name, mixer.clipAction(clip));
    this.rigs.set(actor, { mixer, actions });
    this.setRigAnimation(actor, ['Idle', 'Idle_2']);
  }

  private setRigAnimation(actor: THREE.Object3D, candidates: string[], speed = 1): void {
    const rig = this.rigs.get(actor);
    if (!rig) return;
    const name = candidates.find((candidate) => rig.actions.has(candidate));
    if (!name || rig.currentName === name) {
      if (rig.current) rig.current.timeScale = speed;
      return;
    }
    const next = rig.actions.get(name);
    if (!next) return;
    next.reset().setEffectiveTimeScale(speed).fadeIn(.16).play();
    rig.current?.fadeOut(.16);
    rig.current = next;
    rig.currentName = name;
  }

  private updateRigAnimations(dt: number): void {
    for (const rig of this.rigs.values()) rig.mixer.update(dt);

    const playerSpeed = this.playerVelocity.length();
    this.setRigAnimation(
      this.wolf,
      this.dashTime > 0 ? ['Gallop', 'Walk']
        : this.isGrazing ? ['Eating', 'Idle_2_HeadLow', 'Idle']
          : playerSpeed > .22 ? ['Walk', 'Gallop'] : ['Idle', 'Idle_2'],
      this.dashTime > 0 ? 1.35 : THREE.MathUtils.clamp(playerSpeed / 2.8, .75, 1.25),
    );

    const dogMoving = this.dogVelocity.lengthSq() > .06;
    this.setRigAnimation(
      this.dog,
      this.dogBiteWindup > 0 ? ['Attack', 'Idle_HitReact1']
        : this.dogState === 'chase' ? ['Gallop', 'Walk']
          : dogMoving ? ['Walk', 'Gallop'] : ['Idle', 'Idle_2'],
      this.dogState === 'chase' ? 1.2 : 1,
    );

    this.setRigAnimation(
      this.rival.mesh,
      this.rival.attackWindup > 0 || this.rival.state === 'fight' ? ['Attack', 'Idle_HitReact1']
        : this.rival.state === 'retreat' || this.rival.state === 'carry' ? ['Gallop', 'Walk']
          : this.rival.velocity.lengthSq() > .06 ? ['Walk', 'Gallop'] : ['Idle', 'Idle_2'],
      this.rival.state === 'retreat' ? 1.25 : 1,
    );

    for (const sheep of this.sheep) {
      this.setRigAnimation(
        sheep.mesh,
        sheep.state === 'flee' ? ['Gallop', 'Walk']
          : sheep.state === 'wander' ? ['Walk', 'Idle']
            : sheep.state === 'carried' ? ['Idle_HitReact1', 'Idle']
              : ['Eating', 'Idle_Headlow', 'Idle'],
        sheep.state === 'flee' ? 1.25 : 1,
      );
    }

    for (const animal of this.ambientAnimals) {
      this.setRigAnimation(
        animal.mesh,
        animal.velocity.lengthSq() > .2 ? ['Gallop', 'Walk']
          : animal.velocity.lengthSq() > .01 ? ['Walk', 'Idle'] : ['Eating', 'Idle_Headlow', 'Idle'],
        animal.velocity.lengthSq() > .2 ? 1.1 : .85,
      );
    }
  }

  private createWolf(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'wolf';
    const dark = new THREE.MeshStandardMaterial({ color: 0x3f4448, roughness: .75 });
    const wool = new THREE.MeshStandardMaterial({ color: 0xe8e1ca, roughness: 1 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.62, 1.05, 5, 10), dark);
    body.rotation.z = Math.PI / 2;
    body.position.y = .78;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.ConeGeometry(.55, 1.25, 7), dark);
    head.rotation.z = -Math.PI / 2;
    head.position.set(.95, .95, 0);
    head.castShadow = true;
    const coat = new THREE.Mesh(new THREE.SphereGeometry(.9, 12, 8), wool);
    coat.name = 'coat';
    coat.scale.set(1.15, .85, .85);
    coat.position.y = .82;
    coat.castShadow = true;
    group.add(body, head, coat);
    return group;
  }

  private createSheep(hasBell = false): THREE.Group {
    const group = new THREE.Group();
    const wool = new THREE.MeshStandardMaterial({ color: 0xf3ead4, roughness: 1 });
    const face = new THREE.MeshStandardMaterial({ color: 0x38342f, roughness: 1 });
    const body = new THREE.Mesh(new THREE.SphereGeometry(.68, 10, 8), wool);
    body.scale.set(1.25, .9, .82);
    body.position.y = .72;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.BoxGeometry(.42, .5, .45), face);
    head.position.set(.78, .72, 0);
    head.castShadow = true;
    group.add(body, head);
    if (hasBell) {
      const bell = new THREE.Mesh(
        new THREE.SphereGeometry(.12, 8, 6),
        new THREE.MeshStandardMaterial({ color: 0xd6a62d, metalness: .35, roughness: .45 }),
      );
      bell.position.set(.57, .48, 0);
      bell.name = 'bell';
      group.add(bell);
    }
    return group;
  }

  private createDog(): THREE.Group {
    const group = new THREE.Group();
    const material = new THREE.MeshStandardMaterial({ color: 0x7a4f31, roughness: .8 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.58, 1.15, 5, 9), material);
    body.rotation.z = Math.PI / 2;
    body.position.y = .68;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.BoxGeometry(.75, .72, .7), material);
    head.position.set(.95, .87, 0);
    head.castShadow = true;
    const attention = new THREE.Mesh(
      new THREE.OctahedronGeometry(.2, 0),
      new THREE.MeshBasicMaterial({ color: 0xf2c14e }),
    );
    attention.name = 'attention';
    attention.position.y = 2;
    attention.visible = false;
    group.add(body, head, attention);
    return group;
  }

  private createRival(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'rival';
    const material = new THREE.MeshStandardMaterial({ color: 0x232730, roughness: .78 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.58, 1, 5, 9), material);
    body.rotation.z = Math.PI / 2;
    body.position.y = .72;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.ConeGeometry(.5, 1.05, 7), material);
    head.rotation.z = -Math.PI / 2;
    head.position.set(.9, .88, 0);
    head.castShadow = true;
    const eyes = new THREE.Mesh(
      new THREE.BoxGeometry(.08, .08, .62),
      new THREE.MeshBasicMaterial({ color: 0xd04d31 }),
    );
    eyes.position.set(1.05, 1.03, 0);
    const warning = new THREE.Mesh(
      new THREE.OctahedronGeometry(.18, 0),
      new THREE.MeshBasicMaterial({ color: 0xff5a45 }),
    );
    warning.name = 'attack-warning';
    warning.position.y = 1.95;
    warning.visible = false;
    group.add(body, head, eyes, warning);
    group.visible = false;
    return group;
  }

  private createShepherd(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'shepherd';
    const coat = new THREE.MeshStandardMaterial({ color: 0x34465a, roughness: .85 });
    const skin = new THREE.MeshStandardMaterial({ color: 0xc9936a, roughness: .9 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.38, 1.15, 5, 8), coat);
    body.position.y = 1.05;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.SphereGeometry(.34, 10, 8), skin);
    head.position.y = 1.95;
    head.castShadow = true;
    const gun = new THREE.Mesh(
      new THREE.BoxGeometry(1.35, .1, .1),
      new THREE.MeshStandardMaterial({ color: 0x3a2c22, roughness: .7 }),
    );
    gun.name = 'gun';
    gun.position.set(.7, 1.25, 0);
    group.add(body, head, gun);
    group.position.set(11, 0, -8);
    group.visible = false;
    return group;
  }

  private bindEvents(): void {
    window.addEventListener('keydown', (event) => {
      this.keys.add(event.code);
      if (!event.repeat) this.pressed.add(event.code);
      if (['Space', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(event.code)) event.preventDefault();
      if (event.code === 'Escape' && !event.repeat) this.togglePause();
      if (event.code === 'KeyR' && this.finished && !event.repeat) this.start();
    });
    window.addEventListener('keyup', (event) => this.keys.delete(event.code));
    window.addEventListener('blur', () => {
      this.keys.clear();
      this.pressed.clear();
      if (this.running) this.togglePause();
    });
    document.addEventListener('visibilitychange', () => {
      if (document.hidden && this.running) this.togglePause();
    });
    window.addEventListener('resize', () => this.resize());
    this.renderer.domElement.addEventListener('pointerdown', (event) => {
      this.cameraDragging = true;
      this.cameraPointerX = event.clientX;
      this.cameraPointerY = event.clientY;
      this.renderer.domElement.setPointerCapture(event.pointerId);
    });
    this.renderer.domElement.addEventListener('pointermove', (event) => {
      if (!this.cameraDragging) return;
      const dx = event.clientX - this.cameraPointerX;
      const dy = event.clientY - this.cameraPointerY;
      this.cameraPointerX = event.clientX;
      this.cameraPointerY = event.clientY;
      this.cameraYaw -= dx * .006;
      this.cameraPitch = THREE.MathUtils.clamp(this.cameraPitch + dy * .004, .58, 1.13);
    });
    this.renderer.domElement.addEventListener('pointerup', (event) => {
      this.cameraDragging = false;
      if (this.renderer.domElement.hasPointerCapture(event.pointerId)) {
        this.renderer.domElement.releasePointerCapture(event.pointerId);
      }
    });
    this.renderer.domElement.addEventListener('pointercancel', () => {
      this.cameraDragging = false;
    });
    this.renderer.domElement.addEventListener('wheel', (event) => {
      event.preventDefault();
      this.cameraDistance = THREE.MathUtils.clamp(this.cameraDistance + event.deltaY * .012, 16, 34);
    }, { passive: false });
    ui.start.addEventListener('click', () => {
      if (this.paused) this.resume();
      else this.start();
    });
    ui.sound.addEventListener('click', () => {
      this.soundEnabled = !this.soundEnabled;
      ui.sound.textContent = `Звук: ${this.soundEnabled ? 'вкл' : 'выкл'}`;
      ui.sound.setAttribute('aria-pressed', String(this.soundEnabled));
      try {
        localStorage.setItem('roles-reversed-wolf.sound', this.soundEnabled ? 'on' : 'off');
      } catch {
        // Недоступное хранилище не должно ломать забег.
      }
      if (this.soundEnabled) {
        this.ensureAudio();
        this.playTone(520, .08, .035);
      }
    });
  }

  private consumeKey(...codes: string[]): boolean {
    for (const code of codes) {
      if (!this.pressed.has(code)) continue;
      this.pressed.delete(code);
      return true;
    }
    return false;
  }

  private showFeedback(message: string, duration = 1.5): void {
    this.feedbackMessage = message;
    this.feedbackTime = duration;
  }

  private frame(): void {
    const dt = Math.min(this.clock.getDelta(), .05);
    if (this.running) this.update(dt);
    this.pressed.clear();
    if (!this.paused) this.updateRigAnimations(dt);
    this.renderer.render(this.scene, this.camera);
  }

  private update(dt: number): void {
    this.elapsed += dt;
    this.feedbackTime = Math.max(0, this.feedbackTime - dt);
    this.biteCooldown = Math.max(0, this.biteCooldown - dt);
    this.actionCooldown = Math.max(0, this.actionCooldown - dt);
    this.dashCooldown = Math.max(0, this.dashCooldown - dt);
    this.bleatCooldown = Math.max(0, this.bleatCooldown - dt);
    this.bellNoiseCooldown = Math.max(0, this.bellNoiseCooldown - dt);
    this.lureTime = Math.max(0, this.lureTime - dt);
    if (this.lureTime <= 0) this.luredSheep = undefined;
    this.dashTime = Math.max(0, this.dashTime - dt);
    this.rival.attackCooldown = Math.max(0, this.rival.attackCooldown - dt);
    this.dogRivalCommit = Math.max(0, this.dogRivalCommit - dt);
    this.shepherdReload = Math.max(0, this.shepherdReload - dt);
    if (this.playerHeld > 0) {
      this.playerHeld = Math.max(0, this.playerHeld - dt);
      this.playerHeldElapsed += dt;
      const wantsEscape = this.keys.has('ShiftLeft') || this.keys.has('ShiftRight');
      if (this.playerHeldElapsed >= .15 && wantsEscape && this.dashCooldown <= 0) {
        this.playerHeld = 0;
        this.playerHeldElapsed = 0;
        this.dashCooldown = DASH_COOLDOWN;
        this.dashTime = .18;
        this.dashHitRival = false;
        this.playTone(220, .08, .04, 'triangle');
      }
    }
    this.updatePhase();
    if (this.finished) return;
    if (this.elapsed >= CYCLE_TIME * 3 && this.score < GOAL) {
      this.finish(false, 'Стадо увели', 'Три дня закончились. Пастух усилил охрану и увёл оставшихся овец.');
      return;
    }
    const moved = this.updatePlayer(dt);
    this.updateDisguise(dt, moved);
    this.updateContextActions(dt, moved);
    this.updateScent(dt, moved);
    this.updateRival(dt);
    this.tryBleat();
    this.updateSheep(dt);
    this.updateAmbientAnimals(dt);
    this.updateDog(dt);
    this.updateShepherd(dt);
    this.tryAction();
    this.updateCamera(dt);
    this.updateUi();
  }

  private updatePlayer(dt: number): boolean {
    if (this.playerHeld > 0) {
      this.playerVelocity.multiplyScalar(Math.exp(-20 * dt));
      return false;
    }
    const rawInput = new THREE.Vector3(
      Number(this.keys.has('KeyD') || this.keys.has('ArrowRight')) - Number(this.keys.has('KeyA') || this.keys.has('ArrowLeft')),
      0,
      Number(this.keys.has('KeyS') || this.keys.has('ArrowDown')) - Number(this.keys.has('KeyW') || this.keys.has('ArrowUp')),
    );
    const hasInput = rawInput.lengthSq() > 0;
    if (hasInput) rawInput.normalize();

    // Управление остаётся интуитивным при любом повороте камеры.
    const cameraForward = new THREE.Vector3(-Math.sin(this.cameraYaw), 0, -Math.cos(this.cameraYaw));
    const cameraRight = new THREE.Vector3(Math.cos(this.cameraYaw), 0, -Math.sin(this.cameraYaw));
    const input = cameraRight.multiplyScalar(rawInput.x).addScaledVector(cameraForward, -rawInput.z);
    if (input.lengthSq() > 0) input.normalize();

    const dashPressed = this.consumeKey('ShiftLeft', 'ShiftRight');
    if (dashPressed && this.dashCooldown <= 0 && hasInput) {
      if (this.playerCarrying) this.dropPlayerSheep();
      this.dashTime = .18;
      this.dashCooldown = DASH_COOLDOWN;
      this.dashDirection.copy(input);
      this.dashHitRival = false;
      this.changeProgress = 0;
      if (this.canSee(this.dog.position, this.dogFacing, this.wolf.position, 8, 130)) {
        this.dogSuspicion = Math.min(100, this.dogSuspicion + (this.disguised ? 35 : 15));
        this.dogLastSeen.copy(this.wolf.position);
      }
      this.playTone(180, .08, .035, 'triangle');
      this.emitNoise(this.wolf.position, 6, this.disguised ? 35 : 20);
      this.showFeedback('Рывок: пёс услышал резкое движение', 1.1);
    } else if (dashPressed && this.dashCooldown > 0) {
      this.showFeedback(`Рывок восстановится через ${this.dashCooldown.toFixed(1)} с`, 1);
    }

    const baseSpeed = this.playerCarrying ? 2.7 : this.disguised ? 2.8 : 3.8;
    const speed = this.dashTime > 0 ? 8.5 : baseSpeed;
    const movementDirection = this.dashTime > 0 ? this.dashDirection : input;
    const targetVelocity = movementDirection.clone().multiplyScalar(hasInput || this.dashTime > 0 ? speed : 0);
    const responsiveness = this.dashTime > 0 ? 30 : hasInput ? 9 : 14;
    this.playerVelocity.lerp(targetVelocity, 1 - Math.exp(-responsiveness * dt));
    const previous = this.wolf.position.clone();
    this.wolf.position.addScaledVector(this.playerVelocity, dt);
    this.constrainToMap(this.wolf.position, .85);
    this.resolveObstacles(this.wolf.position, .7, previous);

    if (this.playerVelocity.lengthSq() > .08) {
      const targetAngle = Math.atan2(-this.playerVelocity.z, this.playerVelocity.x);
      const angleDelta = Math.atan2(
        Math.sin(targetAngle - this.wolf.rotation.y),
        Math.cos(targetAngle - this.wolf.rotation.y),
      );
      this.wolf.rotation.y += angleDelta * (1 - Math.exp(-(this.dashTime > 0 ? 18 : 12) * dt));
      this.wolf.position.y = Math.sin(this.elapsed * (this.dashTime > 0 ? 22 : 12)) * .045;
    } else {
      this.wolf.position.y = THREE.MathUtils.lerp(this.wolf.position.y, 0, 1 - Math.exp(-12 * dt));
    }
    return this.playerVelocity.lengthSq() > .12;
  }

  private updateDisguise(dt: number, moved: boolean): void {
    if (!this.keys.has('KeyF')) {
      this.changeProgress = 0;
      return;
    }
    if (this.playerCarrying) {
      this.changeProgress = 0;
      ui.hint.textContent = 'Сначала бросьте или съешьте овцу';
      return;
    }
    if (moved) {
      this.changeProgress = 0;
      ui.hint.textContent = 'Чтобы переодеться, стойте неподвижно';
      return;
    }
    this.changeProgress += dt;
    if (this.changeProgress >= CHANGE_TIME) {
      this.disguised = !this.disguised;
      this.changeProgress = 0;
      this.keys.delete('KeyF');
      this.setDisguiseVisual();
      this.playTone(this.disguised ? 620 : 310, .12, .035);
    }
  }

  private setDisguiseVisual(): void {
    const coat = this.wolf.getObjectByName('coat');
    if (coat) {
      coat.visible = this.disguised;
      if (coat instanceof THREE.Mesh && coat.material instanceof THREE.MeshStandardMaterial) {
        const colors = [0x7e776a, 0xc5beaa, 0xe8e1ca];
        coat.material.color.setHex(colors[this.costumeIntegrity]);
      }
    }
  }

  private updateSheep(dt: number): void {
    for (const sheep of this.sheep) {
      if (!sheep.alive) continue;
      if (sheep.carriedBy === 'player') {
        sheep.state = 'carried';
        const forward = new THREE.Vector3(Math.cos(this.wolf.rotation.y), 0, -Math.sin(this.wolf.rotation.y));
        sheep.mesh.position.copy(this.wolf.position).addScaledVector(forward, .92);
        sheep.mesh.position.y = .42;
        sheep.mesh.rotation.y = this.wolf.rotation.y;
        continue;
      }
      if (sheep.carriedBy === 'rival') {
        sheep.state = 'carried';
        sheep.mesh.position.copy(this.rival.mesh.position).add(new THREE.Vector3(.1, .55, -.65));
        sheep.mesh.rotation.y = this.rival.mesh.rotation.y;
        continue;
      }

      sheep.turnIn -= dt;
      sheep.panicMemory = Math.max(0, sheep.panicMemory - dt);
      const wolfDistance = sheep.mesh.position.distanceTo(this.wolf.position);
      const rivalDistance = this.rival.mesh.visible ? sheep.mesh.position.distanceTo(this.rival.mesh.position) : Infinity;
      const desired = new THREE.Vector3();
      const separation = new THREE.Vector3();
      const cohesion = new THREE.Vector3();
      const alignment = new THREE.Vector3();
      const panicDirection = new THREE.Vector3();
      let neighbors = 0;
      let panickedNeighbors = 0;

      for (const other of this.sheep) {
        if (other === sheep || !other.alive || other.carriedBy) continue;
        const distance = sheep.mesh.position.distanceTo(other.mesh.position);
        if (distance < 4.2) {
          cohesion.add(other.mesh.position);
          alignment.add(other.velocity);
          neighbors += 1;
          if (other.state === 'flee' && distance < 3.1) {
            panicDirection.add(other.velocity);
            panickedNeighbors += 1;
          }
          if (distance < 1.35 && distance > .001) {
            separation.add(sheep.mesh.position.clone().sub(other.mesh.position).multiplyScalar(1 / distance));
          }
        }
      }

      const directlyThreatened = (!this.disguised && wolfDistance < 6.2) || rivalDistance < 5.2;
      if (directlyThreatened) sheep.panicMemory = 1.8;
      else if (panickedNeighbors > 0) sheep.panicMemory = Math.max(sheep.panicMemory, .85);
      const threatened = directlyThreatened || sheep.panicMemory > 0;
      if (threatened) {
        sheep.state = 'flee';
        if (sheep.bell && this.bellNoiseCooldown <= 0) {
          this.bellNoiseCooldown = 3;
          this.emitNoise(sheep.mesh.position, 7, 24, true);
          this.playTone(880, .08, .025, 'triangle');
        }
        if (!this.disguised && wolfDistance < 6.2) {
          desired.add(sheep.mesh.position.clone().sub(this.wolf.position).setY(0).multiplyScalar(1 / Math.max(.4, wolfDistance)));
        }
        if (rivalDistance < 5.2) {
          desired.add(sheep.mesh.position.clone().sub(this.rival.mesh.position).setY(0).multiplyScalar(1 / Math.max(.4, rivalDistance)));
        }
        if (!directlyThreatened && panickedNeighbors > 0 && panicDirection.lengthSq() > .001) {
          desired.add(panicDirection.normalize().multiplyScalar(.7));
        }
        desired.normalize().multiplyScalar(2.65);
        sheep.turnIn = random(.5, 1.1);
      } else if (sheep === this.luredSheep && this.lureTime > 0 && this.disguised) {
        sheep.state = wolfDistance > 1.05 ? 'wander' : 'graze';
        if (wolfDistance > 1.05) {
          desired.copy(this.wolf.position).sub(sheep.mesh.position).setY(0).normalize().multiplyScalar(1.05);
        }
        sheep.turnIn = .4;
      } else {
        if (sheep.turnIn <= 0) {
          sheep.state = Math.random() < .42 ? 'graze' : 'wander';
          sheep.turnIn = sheep.state === 'graze' ? random(1.1, 2.6) : random(1.5, 4.2);
        }
        if (sheep.state === 'wander') {
          const angle = sheep.mesh.rotation.y + random(-1.1, 1.1);
          desired.set(Math.cos(angle), 0, -Math.sin(angle)).multiplyScalar(.75);
        }
        if (neighbors > 0) {
          cohesion.multiplyScalar(1 / neighbors).sub(sheep.mesh.position).setY(0).multiplyScalar(.12);
          alignment.multiplyScalar(1 / neighbors).multiplyScalar(.18);
          desired.add(cohesion).add(alignment);
        }
      }

      desired.add(separation.multiplyScalar(1.5));
      desired.add(this.avoidObstacles(sheep.mesh.position, 2.2).multiplyScalar(1.3));
      const maxSpeed = sheep.state === 'flee' ? 2.65 : sheep.state === 'graze' ? .08 : .9;
      if (desired.lengthSq() > maxSpeed * maxSpeed) desired.setLength(maxSpeed);
      sheep.velocity.lerp(desired, 1 - Math.exp(-(sheep.state === 'flee' ? 8 : 3.5) * dt));

      const previous = sheep.mesh.position.clone();
      sheep.mesh.position.addScaledVector(sheep.velocity, dt);
      this.constrainToMap(sheep.mesh.position, 1.1);
      this.resolveObstacles(sheep.mesh.position, .62, previous);
      if (sheep.velocity.lengthSq() > .015) sheep.mesh.rotation.y = Math.atan2(-sheep.velocity.z, sheep.velocity.x);
      sheep.mesh.position.y = Math.abs(Math.sin(this.elapsed * (sheep.state === 'flee' ? 12 : 6) + sheep.bobOffset)) * (sheep.state === 'flee' ? .1 : .025);
    }
  }

  private updateAmbientAnimals(dt: number): void {
    for (const animal of this.ambientAnimals) {
      animal.turnIn -= dt;
      const wolfDistance = animal.mesh.position.distanceTo(this.wolf.position);
      let targetSpeed = .5;
      if (!this.disguised && wolfDistance < 5.5) {
        animal.wanderDirection.copy(animal.mesh.position).sub(this.wolf.position).setY(0).normalize();
        animal.turnIn = 1.2;
        targetSpeed = 1.65;
      } else if (animal.turnIn <= 0) {
        if (Math.random() < .28) {
          animal.wanderDirection.set(0, 0, 0);
          animal.turnIn = random(1.4, 3.2);
        } else {
          const angle = random(0, Math.PI * 2);
          animal.wanderDirection.set(Math.cos(angle), 0, Math.sin(angle));
          animal.turnIn = random(2.5, 6);
        }
      }

      const desired = animal.wanderDirection.clone().multiplyScalar(targetSpeed);
      desired.add(this.avoidObstacles(animal.mesh.position, 2.6).multiplyScalar(1.25));
      if (desired.lengthSq() > targetSpeed * targetSpeed) desired.setLength(targetSpeed);
      animal.velocity.lerp(desired, 1 - Math.exp(-3.5 * dt));
      const previous = animal.mesh.position.clone();
      animal.mesh.position.addScaledVector(animal.velocity, dt);
      this.constrainToMap(animal.mesh.position, 1.25);
      this.resolveObstacles(animal.mesh.position, .78, previous);
      if (animal.velocity.lengthSq() > .02) {
        animal.mesh.rotation.y = Math.atan2(-animal.velocity.z, animal.velocity.x);
      }
    }
  }

  private updateDog(dt: number): void {
    const night = this.phase === 'Ночь' || this.phase === 'Сумерки';
    const viewRadius = (night ? 5.5 : 7) + this.guardLevel * .25;
    const seesPlayer = this.canSee(this.dog.position, this.dogFacing, this.wolf.position, viewRadius, 110);
    const distance = this.dog.position.distanceTo(this.wolf.position);
    const rivalThreat = this.rival.mesh.visible && this.rival.carrying
      && this.canSee(this.dog.position, this.dogFacing, this.rival.mesh.position, 9, 130);
    if (rivalThreat) this.dogRivalCommit = 1;
    const pursueRival = this.rival.mesh.visible && Boolean(this.rival.carrying)
      && (rivalThreat || this.dogRivalCommit > 0);

    const attention = this.dog.getObjectByName('attention');
    if (attention instanceof THREE.Mesh && attention.material instanceof THREE.MeshBasicMaterial) {
      attention.visible = this.dogState !== 'patrol' && this.dogState !== 'return';
      attention.material.color.setHex(this.dogState === 'chase' ? 0xff493d : this.dogState === 'alert' ? 0xf2c14e : 0x77baf2);
      attention.position.y = 2 + Math.sin(this.elapsed * 8) * .08;
    }

    if (seesPlayer) {
      if (!this.disguised) {
        this.dogSuspicion = Math.min(100, this.dogSuspicion + dt * 260);
        this.dogLastSeen.copy(this.wolf.position);
        this.dogConfirmed = true;
      } else {
        const damageRate = (this.costumeIntegrity === 0 ? 60 : this.costumeIntegrity === 1 ? 20 : 0)
          * (1 + this.guardLevel * .1);
        const closeInspection = distance < 2.8 ? damageRate : 0;
        const unnaturalMovement = this.dashTime > 0 ? 115
          : this.playerVelocity.length() > 3.05 ? 18
            : 0;
        const grazingRelief = this.isGrazing && !this.dogConfirmed ? 14 : 0;
        this.dogSuspicion = THREE.MathUtils.clamp(
          this.dogSuspicion + (closeInspection + unnaturalMovement - grazingRelief) * dt,
          0,
          100,
        );
        if ((this.costumeIntegrity === 0 || unnaturalMovement > 0) && this.dogSuspicion >= 100) this.dogConfirmed = true;
      }
    } else if (this.dogState !== 'chase') {
      this.dogSuspicion = Math.max(0, this.dogSuspicion - dt * 10);
    }

    if (pursueRival) {
      this.moveDogToward(this.rival.mesh.position, 4.35, dt);
      if (this.dog.position.distanceTo(this.rival.mesh.position) < 1.35) {
        this.dropRivalSheep();
        this.rival.state = 'retreat';
        this.rival.hp -= 1;
        this.dogRivalCommit = 0;
        this.playTone(125, .18, .065, 'sawtooth');
      }
      return;
    }

    if (this.dogSuspicion >= 100 && seesPlayer && (!this.disguised || this.dogConfirmed)) this.dogState = 'chase';
    else if (this.dogSuspicion >= 55 && this.dogState === 'patrol') this.dogState = 'alert';

    switch (this.dogState) {
      case 'patrol': {
        const target = this.dogPatrolPoints[this.dogPatrolIndex];
        this.moveDogToward(target, (night ? 2.15 : 1.6) + this.guardLevel * .08, dt);
        if (this.dog.position.distanceTo(target) < .7) {
          this.dogPatrolIndex = (this.dogPatrolIndex + 1) % this.dogPatrolPoints.length;
        }
        break;
      }
      case 'alert':
        this.dogSearchTime += dt;
        if (seesPlayer && this.dogSuspicion > 20) this.moveDogToward(this.wolf.position, 2.1, dt);
        else this.moveDogToward(this.dogLastSeen, 1.8, dt);
        if ((this.dogSuspicion <= 20 && this.dog.position.distanceTo(this.dogLastSeen) < .8)
          || this.dogSearchTime > 3.2) {
          this.dogState = 'return';
          this.dogSearchTime = 0;
        }
        break;
      case 'chase':
        if (seesPlayer && (!this.disguised || this.dogConfirmed)) {
          this.dogLastSeen.copy(this.wolf.position);
          const intercept = this.wolf.position.clone().addScaledVector(this.playerVelocity, Math.min(.55, distance / 12));
          this.moveDogToward(intercept, 4.2 + this.guardLevel * .12, dt);
        } else {
          this.dogState = 'search-visual';
          this.dogSearchTime = 0;
          this.dogBiteWindup = 0;
        }
        break;
      case 'search-visual':
        this.dogSearchTime += dt;
        this.moveDogToward(this.dogLastSeen, 2.5, dt);
        if (seesPlayer && (!this.disguised || this.dogConfirmed)) this.dogState = 'chase';
        else if (this.dog.position.distanceTo(this.dogLastSeen) < .75 || this.dogSearchTime > 4) {
          this.dogState = 'search-scent';
          this.dogSearchTime = 0;
        }
        break;
      case 'search-scent': {
        this.dogSearchTime += dt;
        const scent = this.findLocalScent();
        if (scent) {
          this.moveDogToward(scent.position, 2.25, dt);
          this.dogLastSeen.copy(scent.position);
        } else {
          this.dogVelocity.multiplyScalar(Math.exp(-5 * dt));
          this.dog.rotation.y += dt * 1.4;
        }
        if (seesPlayer && (!this.disguised || this.dogConfirmed)) this.dogState = 'chase';
        else if (this.dogSearchTime > 6 || (this.scents.length === 0 && this.dogSearchTime > 2)) {
          this.dogState = 'return';
          this.dogConfirmed = false;
          this.dogSuspicion = Math.min(this.dogSuspicion, 15);
        }
        break;
      }
      case 'return': {
        const target = this.dogPatrolPoints[this.dogPatrolIndex];
        this.moveDogToward(target, 1.9, dt);
        if (this.dog.position.distanceTo(target) < .8) this.dogState = 'patrol';
        break;
      }
    }

    const canBite = this.dogState === 'chase' && seesPlayer && distance < 1.45 && this.biteCooldown <= 0
      && this.playerHeld <= 0 && this.dashTime <= 0;
    this.dogBiteWindup = canBite ? this.dogBiteWindup + dt : 0;
    if (this.dogBiteWindup >= .3) {
      this.dogBiteWindup = 0;
      const toWolf = this.wolf.position.clone().sub(this.dog.position).setY(0);
      this.maxHealth = Math.max(0, this.maxHealth - 1);
      this.health = Math.min(this.health - 1, this.maxHealth);
      if (this.disguised) {
        this.costumeIntegrity = Math.max(0, this.costumeIntegrity - 1);
        this.setDisguiseVisual();
      }
      if (this.playerCarrying) this.dropPlayerSheep();
      this.biteCooldown = 1.4;
      const shepherdCanHold = this.shepherd.visible && this.shepherd.position.distanceTo(this.dog.position) <= 6;
      if (shepherdCanHold) {
        this.playerHeld = 1.2;
        this.playerHeldElapsed = 0;
      }
      this.playTone(105, .2, .075, 'sawtooth');
      if (toWolf.lengthSq() > .001) this.wolf.position.addScaledVector(toWolf.normalize(), 1.35);
      if (this.health <= 0) this.finish(false, 'Пёс оставил последнюю рану', 'Пёс видит только то, что действительно наблюдал, но на прямой он быстрее. Разрывайте видимость и уводите его на старый запах.');
    }
  }

  private updateScent(dt: number, moved: boolean): void {
    for (let i = this.scents.length - 1; i >= 0; i -= 1) {
      this.scents[i].age += dt;
      if (this.scents[i].age >= 10) this.scents.splice(i, 1);
    }
    if (!this.disguised) this.disguiseScentTail = 2;
    else this.disguiseScentTail = Math.max(0, this.disguiseScentTail - dt);
    this.scentTimer -= dt;
    const leavesScent = !this.disguised || this.disguiseScentTail > 0;
    if (leavesScent && this.scentTimer <= 0) {
      this.scents.push({
        position: this.wolf.position.clone().setY(0),
        age: 0,
        strength: this.playerCarrying ? 1.35 : !this.disguised ? (moved ? 1 : .75) : .3,
      });
      this.scentTimer = moved ? .35 : 1;
      if (this.scents.length > 192) this.scents.splice(0, this.scents.length - 192);
    }
  }

  private updateContextActions(dt: number, moved: boolean): void {
    this.isGrazing = this.keys.has('KeyG') && this.disguised && !moved && !this.playerCarrying && this.playerHeld <= 0;
    if (this.pressed.has('KeyG') && !this.isGrazing) {
      this.showFeedback(!this.disguised ? 'Пастись можно только в овечьей шкуре' : 'Для выпаса остановитесь и не несите добычу');
    }
    if (this.isGrazing && !this.dogConfirmed) {
      this.dogSuspicion = Math.max(0, this.dogSuspicion - dt * 8);
    }

    if (!this.keys.has('KeyE') || moved || this.playerHeld > 0) {
      if (this.pressed.has('KeyE') && moved) this.showFeedback('Для долгого действия сначала остановитесь');
      this.eatProgress = 0;
      this.repairProgress = 0;
      return;
    }

    if (this.playerCarrying && !this.disguised) {
      this.eatProgress += dt;
      this.repairProgress = 0;
      if (this.eatProgress >= 1.6) {
        this.eatProgress = 0;
        this.keys.delete('KeyE');
        this.completeEating();
      }
      return;
    }

    const nearBarn = this.wolf.position.distanceTo(new THREE.Vector3(11, 0, -8)) < 4.5;
    if (nearBarn && this.disguised && this.costumeIntegrity < 2 && this.repairKits > 0) {
      this.repairProgress += dt;
      this.eatProgress = 0;
      if (this.repairProgress >= 2) {
        this.repairProgress = 0;
        this.repairKits -= 1;
        this.costumeIntegrity += 1;
        this.keys.delete('KeyE');
        this.setDisguiseVisual();
        this.playTone(560, .15, .035, 'triangle');
      }
      return;
    }

    if (this.pressed.has('KeyE')) {
      this.showFeedback(this.disguised ? 'E используется для ремонта повреждённой шкуры у сарая' : 'Сначала схватите овцу Пробелом');
    }
    this.eatProgress = 0;
    this.repairProgress = 0;
  }

  private updateRival(dt: number): void {
    const cycle = this.elapsed % CYCLE_TIME;
    const isNight = this.phase === 'Ночь';
    const entryBudget = this.dayNumber >= 3 ? 2 : 1;
    if (isNight && cycle >= this.nextRivalSpawn && cycle < 101
      && this.rival.state === 'hidden' && this.rivalEntriesThisNight < entryBudget) {
      this.spawnRival();
    }
    if ((this.phase === 'Рассвет' || this.phase === 'День') && this.rival.state !== 'hidden') {
      this.dropRivalSheep();
      this.rival.state = 'retreat';
    }
    if (this.rival.state === 'hidden') return;

    const distanceToPlayer = this.rival.mesh.position.distanceTo(this.wolf.position);
    const rivalFacingPlayer = this.wolf.position.clone().sub(this.rival.mesh.position).setY(0);
    const rivalCanReachPlayer = this.canSee(
      this.rival.mesh.position,
      rivalFacingPlayer,
      this.wolf.position,
      1.55,
      220,
    );
    const warning = this.rival.mesh.getObjectByName('attack-warning');
    if (this.dashTime > 0 && distanceToPlayer < 1.65 && rivalCanReachPlayer
      && !this.dashHitRival && this.rival.state !== 'retreat') {
      this.dashHitRival = true;
      this.rival.hp -= 1;
      this.rival.attackWindup = 0;
      this.rival.attackCooldown = .8;
      this.dropRivalSheep();
      const push = this.rival.mesh.position.clone().sub(this.wolf.position).setY(0);
      if (push.lengthSq() > .001) this.rival.mesh.position.addScaledVector(push.normalize(), 1.45);
      this.rival.state = this.rival.hp <= 0 ? 'retreat' : 'fight';
      this.emitNoise(this.wolf.position, 6, 28, true, true);
      this.playTone(190, .1, .055, 'square');
    }

    const preparesAttack = rivalCanReachPlayer && distanceToPlayer < 1.5 && this.rival.attackCooldown <= 0
      && this.rival.state !== 'retreat' && this.dashTime <= 0;
    this.rival.attackWindup = preparesAttack
      ? this.rival.attackWindup + dt
      : Math.max(0, this.rival.attackWindup - dt * 4);
    if (warning) {
      warning.visible = this.rival.attackWindup > 0;
      warning.position.y = 1.95 + Math.sin(this.elapsed * 14) * .1;
    }
    if (this.rival.attackWindup >= .38) {
      this.rival.attackWindup = 0;
      this.health -= 1;
      if (this.disguised) {
        this.costumeIntegrity = Math.max(0, this.costumeIntegrity - 1);
        this.setDisguiseVisual();
      }
      if (this.playerCarrying) this.dropPlayerSheep();
      this.rival.attackCooldown = 1.25;
      this.playTone(150, .12, .05, 'square');
      const knockback = this.wolf.position.clone().sub(this.rival.mesh.position).setY(0);
      if (knockback.lengthSq() > .001) this.wolf.position.addScaledVector(knockback.normalize(), 1);
      if (this.health <= 0) this.finish(false, 'Соперник выиграл схватку', 'Обычные раны можно лечить едой, но прямой бой опасен. Перехватывайте носителя сбоку и используйте рывок.');
    }

    if (this.rival.state === 'retreat') {
      this.moveRivalToward(this.rival.exit, 3.7, dt);
      if (this.rival.mesh.position.distanceTo(this.rival.exit) < .55) this.hideRival();
      return;
    }

    if (!this.rival.target || !this.rival.target.alive || this.rival.target.carriedBy) {
      this.rival.target = this.chooseRivalTarget();
    }
    if (!this.rival.target) {
      this.rival.state = 'retreat';
      return;
    }

    if (this.rival.state === 'approach' || this.rival.state === 'fight') {
      this.moveRivalToward(this.rival.target.mesh.position, 3.35, dt);
      const targetDistance = this.rival.mesh.position.distanceTo(this.rival.target.mesh.position);
      const targetDirection = this.rival.target.mesh.position.clone().sub(this.rival.mesh.position).setY(0);
      if (targetDistance < 1.15
        && this.canSee(this.rival.mesh.position, targetDirection, this.rival.target.mesh.position, 1.2, 220)) {
        this.rival.carrying = this.rival.target;
        this.rival.target.carriedBy = 'rival';
        this.rival.target.state = 'carried';
        this.rival.exit = this.nearestExit(this.rival.mesh.position);
        this.rival.state = 'carry';
        this.playTone(210, .18, .045, 'triangle');
        this.emitNoise(this.rival.mesh.position, 4, 18, true, true);
      }
    } else if (this.rival.state === 'carry' || this.rival.state === 'escape-warning') {
      this.moveRivalToward(this.rival.exit, 2.65, dt);
      const exitDistance = this.rival.mesh.position.distanceTo(this.rival.exit);
      if (exitDistance < 1.8) this.rival.state = 'escape-warning';
      if (this.rival.state === 'escape-warning' && exitDistance < .55) {
        this.rival.exitTimer += dt;
        if (this.rival.exitTimer >= 1.2 && this.rival.carrying) {
          this.rival.carrying.alive = false;
          this.rival.carrying.carriedBy = null;
          this.rival.carrying.mesh.visible = false;
          this.rival.carrying = undefined;
          this.lostSheep += 1;
          this.perfectPossible = false;
          this.playTone(92, .4, .06, 'sawtooth');
          this.hideRival();
          this.checkNoSheepResult();
        }
      } else {
        this.rival.exitTimer = 0;
      }
    }
  }

  private updateShepherd(dt: number): void {
    const cycle = this.elapsed % CYCLE_TIME;
    const shouldBeActive = this.phase === 'Ночь'
      || (this.phase === 'День' && cycle >= 35 - this.guardLevel * 2 && cycle <= 48 + this.guardLevel);
    if (!shouldBeActive) {
      this.shepherdState = 'resting';
      this.shepherd.visible = false;
      this.shepherdAim = 0;
      return;
    }
    if (this.shepherdState === 'resting') {
      this.shepherdState = 'patrol';
      this.shepherd.visible = true;
      this.shepherd.position.set(7.5, 0, -5.2);
    }

    const facing = new THREE.Vector3(Math.cos(this.shepherd.rotation.y), 0, -Math.sin(this.shepherd.rotation.y));
    const seesPlayer = (!this.disguised || (this.playerHeld > 0 && this.dogConfirmed))
      && this.canSee(this.shepherd.position, facing, this.wolf.position, 8, 100);
    if (seesPlayer && this.shepherdReload <= 0) {
      this.shepherdState = 'aim';
      this.shepherdAim += dt;
      const direction = this.wolf.position.clone().sub(this.shepherd.position).setY(0).normalize();
      this.shepherd.rotation.y = Math.atan2(-direction.z, direction.x);
      const aimDuration = this.playerHeld > 0 ? .45 : .9;
      if (this.shepherdAim >= aimDuration) {
        this.shepherdAim = 0;
        this.shepherdReload = Math.max(1.9, 2.5 - this.guardLevel * .15);
        this.shepherdState = 'reload';
        this.playTone(70, .28, .09, 'square');
        if (this.dashTime > 0) {
          this.playTone(310, .09, .035, 'triangle');
        } else if (this.canSee(this.shepherd.position, direction, this.wolf.position, 8.4, 16)) {
          this.finish(false, 'Пастух попал в цель', 'Прицеливание заметно заранее. Разрывайте линию видимости за крупным укрытием или уходите рывком в сторону.');
        }
      }
      return;
    }

    this.shepherdAim = Math.max(0, this.shepherdAim - dt * 2.5);
    if (this.shepherdReload > 0) this.shepherdState = 'reload';
    else if (this.dogState === 'chase' || this.dogState === 'alert') {
      this.shepherdState = 'investigate';
      this.moveShepherdToward(this.dogLastSeen, 1.8, dt);
    } else {
      this.shepherdState = 'patrol';
      const target = this.shepherdPatrolPoints[this.shepherdPatrolIndex];
      this.moveShepherdToward(target, 1.35, dt);
      if (this.shepherd.position.distanceTo(target) < .6) {
        this.shepherdPatrolIndex = (this.shepherdPatrolIndex + 1) % this.shepherdPatrolPoints.length;
      }
    }
  }

  private tryBleat(): void {
    if (!this.consumeKey('KeyQ')) return;
    if (!this.disguised) {
      this.showFeedback('Блеять можно только в овечьей шкуре');
      return;
    }
    if (this.playerHeld > 0) {
      this.showFeedback('Сначала вырвитесь из хватки пса');
      return;
    }
    if (this.bleatCooldown > 0) {
      this.showFeedback(`Приманка восстановится через ${this.bleatCooldown.toFixed(1)} с`);
      return;
    }
    this.bleatCooldown = 6;
    this.bleatTimes.push(this.elapsed);
    while (this.bleatTimes.length > 0 && this.elapsed - this.bleatTimes[0] > 15) this.bleatTimes.shift();

    let target: Sheep | undefined;
    let targetDistance = 4.5;
    for (const sheep of this.sheep) {
      if (!sheep.alive || sheep.carriedBy || sheep.state === 'flee') continue;
      const distance = sheep.mesh.position.distanceTo(this.wolf.position);
      if (distance < targetDistance) {
        target = sheep;
        targetDistance = distance;
      }
    }
    this.luredSheep = target;
    this.lureTime = target ? 2.5 : 0;
    const repeated = this.bleatTimes.length >= 3;
    if (repeated) this.emitNoise(this.wolf.position, 6, 38, true);
    this.playTone(target ? 510 : 390, .16, .035, 'triangle');
    this.showFeedback(target ? 'Ближайшая спокойная овца заинтересовалась' : 'Рядом нет спокойной овцы', 1.4);
  }

  private tryAction(): void {
    if (!this.consumeKey('Space')) return;
    if (this.actionCooldown > 0) {
      this.showFeedback('Действие ещё восстанавливается', .8);
      return;
    }
    if (this.disguised) {
      this.showFeedback('Чтобы хватать и атаковать, сначала снимите шкуру');
      return;
    }
    if (this.playerCarrying) {
      this.dropPlayerSheep();
      this.actionCooldown = .3;
      this.showFeedback('Добыча отпущена', 1);
      return;
    }
    const playerFacing = new THREE.Vector3(Math.cos(this.wolf.rotation.y), 0, -Math.sin(this.wolf.rotation.y));
    if (this.rival.mesh.visible && this.rival.mesh.position.distanceTo(this.wolf.position) < 2.25
      && this.canSee(this.wolf.position, playerFacing, this.rival.mesh.position, 2.3, 240)) {
      this.rival.hp -= 1;
      this.rival.state = this.rival.hp <= 0 ? 'retreat' : 'fight';
      this.rival.attackWindup = 0;
      this.dropRivalSheep();
      const push = this.rival.mesh.position.clone().sub(this.wolf.position).setY(0);
      if (push.lengthSq() > .001) this.rival.mesh.position.addScaledVector(push.normalize(), 1.2);
      this.actionCooldown = .55;
      this.playTone(165, .1, .055, 'square');
      this.emitNoise(this.wolf.position, 6, 35, true, true);
      this.showFeedback(this.rival.hp <= 0 ? 'Соперник отступает' : `Удар по сопернику · ${this.rival.hp} HP`, 1.2);
      return;
    }
    if (this.victoryPending) return;
    let nearest: Sheep | undefined;
    let nearestDistance = 2.05;
    for (const sheep of this.sheep) {
      if (!sheep.alive || sheep.carriedBy) continue;
      const distance = sheep.mesh.position.distanceTo(this.wolf.position);
      if (distance < nearestDistance
        && this.canSee(this.wolf.position, playerFacing, sheep.mesh.position, 2.1, 240)) {
        nearest = sheep;
        nearestDistance = distance;
      }
    }
    if (!nearest) {
      this.showFeedback('Подойдите ближе и повернитесь к овце');
      return;
    }
    this.playerCarrying = nearest;
    nearest.carriedBy = 'player';
    nearest.state = 'carried';
    nearest.velocity.set(0, 0, 0);
    this.emitNoise(this.wolf.position, 4, 25, true, true);
    this.playTone(230, .11, .04, 'triangle');
    this.actionCooldown = .45;
    this.showFeedback('Овца в зубах: удерживайте E, чтобы съесть', 1.5);
  }

  private completeEating(): void {
    const sheep = this.playerCarrying;
    if (!sheep) return;
    sheep.alive = false;
    sheep.carriedBy = null;
    sheep.mesh.visible = false;
    this.playerCarrying = undefined;
    this.score += 1;
    this.health = Math.min(this.maxHealth, this.health + 2);
    this.emitNoise(this.wolf.position, 5, 45, true, true);
    this.playTone(245 + this.score * 55, .16, .06);
    this.actionCooldown = 1.1;
    if (this.score >= GOAL) {
      this.victoryPending = true;
      this.playTone(620, .22, .05, 'triangle');
    } else {
      this.checkNoSheepResult();
    }
  }

  private dropPlayerSheep(): void {
    const sheep = this.playerCarrying;
    if (!sheep) return;
    sheep.carriedBy = null;
    sheep.state = 'flee';
    sheep.mesh.visible = true;
    const forward = new THREE.Vector3(Math.cos(this.wolf.rotation.y), 0, -Math.sin(this.wolf.rotation.y));
    sheep.mesh.position.copy(this.wolf.position).addScaledVector(forward, 1.1).setY(0);
    sheep.velocity.copy(forward).multiplyScalar(1.8);
    sheep.turnIn = .65;
    this.playerCarrying = undefined;
    this.eatProgress = 0;
  }

  private spawnRival(): void {
    const entrances = [
      new THREE.Vector3(-15, 0, -7),
      new THREE.Vector3(-15, 0, 7),
      new THREE.Vector3(15, 0, 6),
    ];
    const safe = entrances.filter((point) => point.distanceTo(this.wolf.position) >= 6);
    const spawn = (safe.length > 0 ? safe : entrances)[Math.floor(Math.random() * (safe.length || entrances.length))];
    this.rival.mesh.position.copy(spawn);
    this.rival.mesh.visible = true;
    this.rival.state = 'approach';
    this.rival.hp = 3 + Math.floor(this.guardLevel / 2);
    this.rival.exitTimer = 0;
    this.rival.attackWindup = 0;
    this.rivalEntriesThisNight += 1;
    this.rival.target = this.chooseRivalTarget();
    this.rival.exit = this.nearestExit(spawn);
    this.playTone(145, .45, .035, 'triangle');
  }

  private hideRival(): void {
    this.dropRivalSheep();
    this.rival.mesh.visible = false;
    this.rival.state = 'hidden';
    this.rival.target = undefined;
    this.rival.velocity.set(0, 0, 0);
    this.rival.exitTimer = 0;
    this.rival.attackWindup = 0;
    const warning = this.rival.mesh.getObjectByName('attack-warning');
    if (warning) warning.visible = false;
    this.nextRivalSpawn = Math.min(101, (this.elapsed % CYCLE_TIME) + 9);
  }

  private dropRivalSheep(): void {
    const carried = this.rival.carrying;
    if (!carried) return;
    carried.carriedBy = null;
    carried.state = 'flee';
    carried.mesh.visible = true;
    carried.mesh.position.copy(this.rival.mesh.position).add(new THREE.Vector3(0, 0, .8));
    const away = carried.mesh.position.clone().sub(this.rival.mesh.position).setY(0);
    carried.velocity.copy(away.lengthSq() > .001 ? away.normalize().multiplyScalar(2.2) : new THREE.Vector3(0, 0, 2.2));
    carried.turnIn = .7;
    this.rival.carrying = undefined;
    this.rival.exitTimer = 0;
  }

  private chooseRivalTarget(): Sheep | undefined {
    let best: Sheep | undefined;
    let bestScore = Infinity;
    for (const sheep of this.sheep) {
      if (!sheep.alive || sheep.carriedBy) continue;
      const dogRisk = Math.max(0, 6 - sheep.mesh.position.distanceTo(this.dog.position)) * 1.8;
      const playerCompetition = Math.max(0, 3 - sheep.mesh.position.distanceTo(this.wolf.position));
      const score = sheep.mesh.position.distanceTo(this.rival.mesh.position) + dogRisk + playerCompetition;
      if (score < bestScore) {
        best = sheep;
        bestScore = score;
      }
    }
    return best;
  }

  private nearestExit(position: THREE.Vector3): THREE.Vector3 {
    const exits = [
      new THREE.Vector3(-15.3, 0, -7),
      new THREE.Vector3(-15.3, 0, 7),
      new THREE.Vector3(15.3, 0, 6),
      new THREE.Vector3(0, 0, -11.3),
    ];
    return exits.reduce((best, point) => point.distanceTo(position) < best.distanceTo(position) ? point : best).clone();
  }

  private moveDogToward(target: THREE.Vector3, speed: number, dt: number): void {
    const direction = target.clone().sub(this.dog.position).setY(0);
    if (direction.lengthSq() > .02) direction.normalize().multiplyScalar(speed);
    direction.add(this.avoidObstacles(this.dog.position, 2.5).multiplyScalar(speed));
    if (direction.lengthSq() > speed * speed) direction.setLength(speed);
    this.dogVelocity.lerp(direction, 1 - Math.exp(-8 * dt));
    const previous = this.dog.position.clone();
    this.dog.position.addScaledVector(this.dogVelocity, dt);
    this.constrainToMap(this.dog.position, .8);
    this.resolveObstacles(this.dog.position, .7, previous);
    if (this.dogVelocity.lengthSq() > .04) {
      this.dogFacing.copy(this.dogVelocity).normalize();
      this.dog.rotation.y = Math.atan2(-this.dogFacing.z, this.dogFacing.x);
      this.dog.position.y = Math.abs(Math.sin(this.elapsed * 13)) * .05;
    }
  }

  private moveRivalToward(target: THREE.Vector3, speed: number, dt: number): void {
    const direction = target.clone().sub(this.rival.mesh.position).setY(0);
    if (direction.lengthSq() > .02) direction.normalize().multiplyScalar(speed);
    direction.add(this.avoidObstacles(this.rival.mesh.position, 2.2).multiplyScalar(speed));
    const fromDog = this.rival.mesh.position.clone().sub(this.dog.position).setY(0);
    const dogDistance = fromDog.length();
    if (dogDistance < 4.8 && dogDistance > .001) {
      direction.add(fromDog.normalize().multiplyScalar((4.8 - dogDistance) * .75));
    }
    if (direction.lengthSq() > speed * speed) direction.setLength(speed);
    this.rival.velocity.lerp(direction, 1 - Math.exp(-8 * dt));
    const previous = this.rival.mesh.position.clone();
    this.rival.mesh.position.addScaledVector(this.rival.velocity, dt);
    this.constrainToMap(this.rival.mesh.position, .45);
    this.resolveObstacles(this.rival.mesh.position, .65, previous);
    if (this.rival.velocity.lengthSq() > .04) {
      this.rival.mesh.rotation.y = Math.atan2(-this.rival.velocity.z, this.rival.velocity.x);
      this.rival.mesh.position.y = Math.abs(Math.sin(this.elapsed * 12 + 1.7)) * .055;
    }
  }

  private moveShepherdToward(target: THREE.Vector3, speed: number, dt: number): void {
    const direction = target.clone().sub(this.shepherd.position).setY(0);
    if (direction.lengthSq() < .02) return;
    direction.normalize();
    const previous = this.shepherd.position.clone();
    this.shepherd.position.addScaledVector(direction, speed * dt);
    this.constrainToMap(this.shepherd.position, .8);
    this.resolveObstacles(this.shepherd.position, .55, previous);
    this.shepherd.rotation.y = Math.atan2(-direction.z, direction.x);
    this.shepherd.position.y = Math.abs(Math.sin(this.elapsed * 8)) * .025;
  }

  private constrainToMap(position: THREE.Vector3, margin: number): void {
    position.x = THREE.MathUtils.clamp(position.x, -MAP_W / 2 + margin, MAP_W / 2 - margin);
    position.z = THREE.MathUtils.clamp(position.z, -MAP_H / 2 + margin, MAP_H / 2 - margin);
  }

  private resolveObstacles(position: THREE.Vector3, radius: number, previous: THREE.Vector3): void {
    for (const obstacle of this.obstacles) {
      const offset = position.clone().sub(obstacle.position).setY(0);
      const minimum = obstacle.radius + radius;
      if (offset.lengthSq() < minimum * minimum) {
        if (offset.lengthSq() < .0001) position.copy(previous);
        else position.copy(obstacle.position).add(offset.setLength(minimum));
      }
    }
  }

  private avoidObstacles(position: THREE.Vector3, influence: number): THREE.Vector3 {
    const force = new THREE.Vector3();
    for (const obstacle of this.obstacles) {
      const offset = position.clone().sub(obstacle.position).setY(0);
      const distance = offset.length();
      const range = obstacle.radius + influence;
      if (distance < range && distance > .001) force.add(offset.normalize().multiplyScalar((range - distance) / range));
    }
    return force;
  }

  private canSee(origin: THREE.Vector3, facing: THREE.Vector3, target: THREE.Vector3, radius: number, angleDegrees: number): boolean {
    const toTarget = target.clone().sub(origin).setY(0);
    const distance = toTarget.length();
    if (distance > radius) return false;
    if (distance > .8) {
      const direction = toTarget.clone().normalize();
      const normalizedFacing = facing.lengthSq() > .001 ? facing.clone().normalize() : new THREE.Vector3(1, 0, 0);
      if (normalizedFacing.dot(direction) < Math.cos(THREE.MathUtils.degToRad(angleDegrees / 2))) return false;
    }
    for (const obstacle of this.obstacles) {
      if (distancePointToSegment(obstacle.position, origin, target) < obstacle.radius * .82) return false;
    }
    return true;
  }

  private findLocalScent(): ScentMark | undefined {
    let best: ScentMark | undefined;
    let bestValue = -Infinity;
    for (const mark of this.scents) {
      const freshness = Math.max(0, 1 - mark.age / 10);
      const strength = mark.strength * freshness * freshness;
      const perception = 2.4 * Math.sqrt(Math.min(1, strength));
      const distance = mark.position.distanceTo(this.dog.position);
      if (distance <= perception && strength - distance * .08 > bestValue) {
        best = mark;
        bestValue = strength - distance * .08;
      }
    }
    return best;
  }

  private emitNoise(
    position: THREE.Vector3,
    radius: number,
    suspicion: number,
    investigate = true,
    scareSheep = false,
  ): void {
    if (this.dog.position.distanceTo(position) <= radius) {
      this.dogLastSeen.copy(position);
      this.dogSuspicion = Math.min(100, this.dogSuspicion + suspicion);
      if (investigate && (this.dogState === 'patrol' || this.dogState === 'return')) {
        this.dogState = 'alert';
        this.dogSearchTime = 0;
      }
    }
    if (investigate && this.shepherd.visible && this.shepherd.position.distanceTo(position) <= radius + 2
      && this.shepherdState !== 'aim') {
      this.shepherdState = 'investigate';
    }
    if (scareSheep) {
      for (const sheep of this.sheep) {
        if (!sheep.alive || sheep.carriedBy) continue;
        const distance = sheep.mesh.position.distanceTo(position);
        if (distance > radius) continue;
        sheep.state = 'flee';
        sheep.turnIn = Math.max(sheep.turnIn, 1.2);
        const away = sheep.mesh.position.clone().sub(position).setY(0);
        if (away.lengthSq() > .001) sheep.velocity.addScaledVector(away.normalize(), 1.3);
      }
    }
  }

  private checkNoSheepResult(): void {
    if (this.score >= GOAL) return;
    const remaining = this.sheep.filter((sheep) => sheep.alive).length;
    if (remaining === 0) {
      this.finish(false, 'Стадо закончилось', `Соперники унесли овец: ${this.lostSheep}. Для идеальной охоты нельзя позволять им покинуть карту с добычей.`);
    }
  }

  private updatePhase(): void {
    const currentCycle = Math.floor(this.elapsed / CYCLE_TIME);
    if (currentCycle > this.cycleIndex) {
      this.cycleIndex = currentCycle;
      this.dayNumber = currentCycle + 1;
      this.guardLevel = Math.min(3, currentCycle);
      this.repairKits = Math.min(2, this.repairKits + 1);
    }
    const t = this.elapsed % CYCLE_TIME;
    if (t < 50) this.phase = 'День';
    else if (t < 60) this.phase = 'Сумерки';
    else if (t < 110) this.phase = 'Ночь';
    else this.phase = 'Рассвет';

    if (this.phase !== this.previousPhase) {
      if (this.phase === 'Ночь') {
        this.rivalEntriesThisNight = 0;
        this.nextRivalSpawn = 66;
        this.playTone(170, .3, .025, 'triangle');
      }
      if (this.phase === 'День' && this.victoryPending && this.elapsed >= CYCLE_TIME) {
        const title = this.perfectPossible ? 'Идеальная охота' : 'Охота завершена';
        const text = this.perfectPossible
          ? 'Вы выполнили квоту, пережили ночную охоту и не отдали сопернику ни одной овцы.'
          : `Вы выполнили квоту и пережили рассвет, но соперник унёс овец: ${this.lostSheep}.`;
        this.finish(true, title, text);
        return;
      }
      this.previousPhase = this.phase;
    }

    const nightFactor = t < 50 ? 0 : t < 60 ? smoothstep((t - 50) / 10) : t < 110 ? 1 : 1 - smoothstep((t - 110) / 10);
    const day = new THREE.Color(0xaacb8b);
    const night = new THREE.Color(0x121b2b);
    const color = day.clone().lerp(night, nightFactor);
    this.scene.background = color;
    if (this.scene.fog instanceof THREE.Fog) this.scene.fog.color.copy(color);
    this.sun.intensity = THREE.MathUtils.lerp(2.1, .35, nightFactor);
    this.sky.intensity = THREE.MathUtils.lerp(1.6, .45, nightFactor);
    for (const light of this.lanterns) light.intensity = THREE.MathUtils.lerp(.35, 3.2, nightFactor);
  }

  private updateCamera(dt: number): void {
    const rotateInput = Number(this.keys.has('KeyX')) - Number(this.keys.has('KeyZ'));
    this.cameraYaw += rotateInput * dt * 1.15;
    const lookAhead = this.wolf.position.clone().addScaledVector(this.playerVelocity, .65);
    this.cameraTarget.lerp(lookAhead, 1 - Math.exp(-4.5 * dt));
    const dynamicDistance = this.cameraDistance + (this.dashTime > 0 ? 1.8 : 0);
    const horizontal = Math.cos(this.cameraPitch) * dynamicDistance;
    const desired = new THREE.Vector3(
      this.cameraTarget.x + Math.sin(this.cameraYaw) * horizontal,
      Math.sin(this.cameraPitch) * dynamicDistance,
      this.cameraTarget.z + Math.cos(this.cameraYaw) * horizontal,
    );
    this.camera.position.lerp(desired, 1 - Math.exp(-5 * dt));
    this.camera.fov = THREE.MathUtils.lerp(this.camera.fov, this.dashTime > 0 ? 47 : 42, 1 - Math.exp(-9 * dt));
    this.camera.updateProjectionMatrix();
    this.camera.lookAt(this.cameraTarget.x, .55, this.cameraTarget.z);
  }

  private updateUi(): void {
    const seconds = Math.floor(this.elapsed % CYCLE_TIME);
    ui.phase.textContent = this.phase;
    ui.day.textContent = `День ${this.dayNumber} · охрана ${this.guardLevel + 1}`;
    ui.time.textContent = `${String(Math.floor(seconds / 60)).padStart(2, '0')}:${String(seconds % 60).padStart(2, '0')}`;
    ui.sheep.textContent = this.victoryPending ? 'Квота выполнена · переживите рассвет' : `Добыча: ${this.score} / ${GOAL}`;
    ui.lost.textContent = `Потери: ${this.lostSheep}`;
    ui.health.textContent = `Здоровье: ${this.health} / ${this.maxHealth}`;
    ui.form.textContent = `Маскировка: ${this.disguised ? 'надета' : 'снята'}`;
    const costumeLabels = ['порвана', 'повреждена', 'цела'];
    ui.costume.textContent = `Шкура: ${costumeLabels[this.costumeIntegrity]} · ремкомплекты ${this.repairKits}`;
    ui.carrying.textContent = `Добыча в зубах: ${this.playerCarrying ? 'да' : 'нет'}`;
    const progress = this.eatProgress > 0
      ? this.eatProgress / 1.6
      : this.repairProgress > 0
        ? this.repairProgress / 2
        : this.changeProgress / CHANGE_TIME;
    ui.progress.style.width = `${Math.min(100, progress * 100)}%`;

    const dogLabels: Record<DogState, string> = {
      patrol: 'патрулирует',
      alert: 'проверяет подозрение',
      chase: this.dogBiteWindup > 0 ? 'готовит укус!' : 'преследует',
      'search-visual': 'идёт к последней точке',
      'search-scent': 'ищет по запаху',
      return: 'возвращается к стаду',
    };
    ui.danger.textContent = `Пёс: ${dogLabels[this.dogState]} · ${Math.round(this.dogSuspicion)}%`;
    const rivalLabels: Record<RivalState, string> = {
      hidden: 'пока не замечен',
      approach: 'крадётся к стаду',
      carry: 'уносит овцу',
      fight: `дерётся · ${this.rival.hp} HP`,
      retreat: 'отступает',
      'escape-warning': `почти у выхода · ${Math.max(0, 1.2 - this.rival.exitTimer).toFixed(1)} с`,
    };
    ui.rival.textContent = `Соперник: ${this.rival.attackWindup > 0 ? 'готовит бросок!' : rivalLabels[this.rival.state]}`;
    ui.dash.textContent = `Рывок: ${this.dashCooldown <= 0 ? 'готов' : `${this.dashCooldown.toFixed(1)} с`} · приманка: ${this.bleatCooldown <= 0 ? 'готова' : `${this.bleatCooldown.toFixed(1)} с`}`;
    ui.models.textContent = this.modelStatus;
    const nearBarn = this.wolf.position.distanceTo(new THREE.Vector3(11, 0, -8)) < 4.5;
    if (this.feedbackTime > 0) ui.hint.textContent = this.feedbackMessage;
    else if (this.playerHeld > 0) ui.hint.textContent = `Пёс удерживает: ${this.playerHeld.toFixed(1)} с — Shift для рывка!`;
    else if (this.eatProgress > 0) ui.hint.textContent = `Поедание: ${Math.max(0, 1.6 - this.eatProgress).toFixed(1)} с`;
    else if (this.repairProgress > 0) ui.hint.textContent = `Ремонт маскировки: ${Math.max(0, 2 - this.repairProgress).toFixed(1)} с`;
    else if (this.changeProgress > 0) ui.hint.textContent = `Переодевание: ${Math.ceil(CHANGE_TIME - this.changeProgress)} с`;
    else if (this.isGrazing) ui.hint.textContent = 'Притворно пасётесь: подозрение снижается';
    else if (this.shepherdState === 'aim') {
      const aimDuration = this.playerHeld > 0 ? .45 : .9;
      ui.hint.textContent = `Пастух целится: ${Math.max(0, aimDuration - this.shepherdAim).toFixed(1)} с — уйдите за укрытие!`;
    }
    else if (this.rival.state === 'escape-warning') ui.hint.textContent = 'Соперник почти ушёл! Сбейте его рывком или ударьте Пробелом';
    else if (this.victoryPending) ui.hint.textContent = 'Квота выполнена. Не рискуйте — переживите рассвет';
    else if (this.playerCarrying) ui.hint.textContent = 'Удерживайте E, чтобы съесть овцу; Пробел — бросить';
    else if (nearBarn && this.disguised && this.costumeIntegrity < 2 && this.repairKits > 0) ui.hint.textContent = 'Удерживайте E у сарая, чтобы починить шкуру';
    else if (!this.disguised) ui.hint.textContent = 'Пробел рядом с овцой — схватить; рядом с соперником — ударить';
    else if (this.phase === 'Ночь') ui.hint.textContent = 'Ночью пёс ищет активнее. Не отходите от стада';
    else ui.hint.textContent = 'Удерживайте F неподвижно, чтобы снять маскировку';
  }

  private finish(won: boolean, title: string, text: string): void {
    this.running = false;
    this.finished = true;
    this.paused = false;
    ui.overlayTitle.textContent = title;
    ui.overlayText.textContent = text;
    ui.start.textContent = won ? 'Сыграть ещё раз' : 'Попробовать снова';
    ui.overlay.classList.remove('hidden');
    this.playTone(won ? 659 : 130, .35, .065, won ? 'sine' : 'sawtooth');
  }

  private ensureAudio(): void {
    if (!this.audioContext) this.audioContext = new AudioContext();
    if (this.audioContext.state === 'suspended') void this.audioContext.resume();
  }

  private playTone(frequency: number, duration: number, volume: number, type: OscillatorType = 'sine'): void {
    if (!this.soundEnabled || !this.audioContext) return;
    const oscillator = this.audioContext.createOscillator();
    const gain = this.audioContext.createGain();
    oscillator.type = type;
    oscillator.frequency.value = frequency;
    gain.gain.setValueAtTime(volume, this.audioContext.currentTime);
    gain.gain.exponentialRampToValueAtTime(.0001, this.audioContext.currentTime + duration);
    oscillator.connect(gain).connect(this.audioContext.destination);
    oscillator.start();
    oscillator.stop(this.audioContext.currentTime + duration);
  }

  private togglePause(): void {
    if (this.finished) return;
    if (this.paused) {
      this.resume();
      return;
    }
    if (!this.running) return;
    this.running = false;
    this.paused = true;
    this.keys.clear();
    ui.overlayTitle.textContent = 'Пауза';
    ui.overlayText.textContent = 'Забег остановлен. Прогресс сохранён.';
    ui.start.textContent = 'Продолжить';
    ui.overlay.classList.remove('hidden');
  }

  private resume(): void {
    this.paused = false;
    this.running = true;
    this.keys.clear();
    ui.overlay.classList.add('hidden');
    this.clock.getDelta();
  }

  private resetSheep(): void {
    for (const sheep of this.sheep) {
      sheep.alive = true;
      sheep.mesh.visible = true;
      const spawn = new THREE.Vector3();
      for (let attempt = 0; attempt < 24; attempt += 1) {
        spawn.set(random(-12, 9), 0, random(-8, 8));
        const clearOfObstacle = this.obstacles.every(
          (obstacle) => spawn.distanceTo(obstacle.position) > obstacle.radius + .9,
        );
        if (clearOfObstacle) break;
      }
      sheep.mesh.position.copy(spawn);
      sheep.velocity.set(0, 0, 0);
      sheep.turnIn = random(0, 2);
      sheep.state = 'graze';
      sheep.carriedBy = null;
      sheep.panicMemory = 0;
    }
  }

  private resize(): void {
    this.camera.aspect = window.innerWidth / window.innerHeight;
    this.camera.updateProjectionMatrix();
    this.renderer.setSize(window.innerWidth, window.innerHeight);
  }
}

function random(min: number, max: number): number {
  return min + Math.random() * (max - min);
}

function smoothstep(value: number): number {
  const t = THREE.MathUtils.clamp(value, 0, 1);
  return t * t * (3 - 2 * t);
}

function distancePointToSegment(point: THREE.Vector3, start: THREE.Vector3, end: THREE.Vector3): number {
  const segment = end.clone().sub(start).setY(0);
  const toPoint = point.clone().sub(start).setY(0);
  const lengthSq = segment.lengthSq();
  if (lengthSq <= .0001) return toPoint.length();
  const t = THREE.MathUtils.clamp(toPoint.dot(segment) / lengthSq, 0, 1);
  return start.clone().addScaledVector(segment, t).distanceTo(point);
}

new PrototypeGame(required('game'));
