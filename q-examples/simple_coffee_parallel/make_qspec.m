% generate qspec for top-level models
clear,clc
% proj_startup;

% config
appinfo= matlab.apputil.getInstalledAppInfo;
addpath(genpath(appinfo.location));

slxNames= [
    {'simple_coffee'}
    ];

%% find
for slxN=1:length(slxNames)
    clear rt bd ch chNames qpath
    slxName= slxNames{slxN};

    slxHandle= load_system(slxName);

    rt = sfroot;

    bd = rt.find('-isa','Simulink.BlockDiagram');
    ch = bd.find('-isa','Stateflow.Chart');

    if isempty(ch) %find referenced libraries
        slxLibs=libinfo(slxHandle);
        for nlibs= 1:length(slxLibs), load_system(slxLibs(nlibs).Library), end
        bd = rt.find('-isa','Simulink.BlockDiagram');
        ch = bd.find('-isa','Stateflow.Chart');
    end
    assert(~isempty(ch),'Stateflow chart not found!')


    for nch=1:length(ch)
        chNames{nch}= ch(nch).Name;
    end
    disp(chNames)

    %% speckle
    for nch= 1:length(chNames)
        skipDataInit= false; removePriorities= false;

        qOut{slxN}{nch}= qspklr(...
            'stateflowParse',true,...
            'slxFile',slxName,...
            'chartName',chNames{nch},...
            'qspecWrite',true,...
            'skipDataInit',skipDataInit,...
            'removePriorities',removePriorities,...
            'qspecName',chNames{nch});

        % organize
        qpath= ['qspec/'  slxNames{slxN} '/' chNames{nch}];

        if isfile([qpath '/props-' chNames{nch} '.qi'])
            delete(['props-' chNames{nch} '.qi'])
        end
        movefile(['*' chNames{nch} '.q*'],qpath)
    end
    try rmdir slprj s, delete *.slxc, end
end